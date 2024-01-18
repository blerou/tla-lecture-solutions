-------------------------- MODULE MyTwoPhaseCommit --------------------------

CONSTANTS RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]

TPTypeOK == 
  /\ rmState \in [RM |-> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in { "init", "done" }
  /\ tmPrepared \subseteq RM
  /\ msgs \in Messages
  
TPInit ==
  /\ rmState = [ r \in RM |-> "working" ]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}
  
TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \union {r}
  /\ UNCHANGED << rmState, tmState, msgs >>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ msgs' = msgs \union [type |-> "Commit"]
  /\ tmState' = "done"
  /\ UNCHANGED << rmState, tmPrepared >>
  
TMAbort ==
  /\ tmState = "init"
\*  /\ \E r \in RM: rmState[r] = "aborted"
  /\ msgs' = msgs \union [type |-> "Abort"]
  /\ tmState' = "done"
  /\ UNCHANGED << rmState, tmPrepared >>

RMPrepared(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \union [type |-> "Prepared", rm |-> r]
  /\ UNCHANGED << tmState, tmPrepared >>
  
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED << tmState, tmPrepared, msgs >>

RMRcvCommitMsg(r) ==
  /\ rmState[r] = "prepared"
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "commited"]
  /\ UNCHANGED << tmState, tmPrepared, msgs >>
 
RMRcvAbortMsg(r) ==
  /\ rmState[r] = {"working", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED << tmState, tmPrepared, msgs >>
 
TPNext == 
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM: 
      \/ TMRcvPrepared(r) 
      \/ RMPrepared(r)
      \/ RMChooseToAbort(r)
      \/ RMRcvCommitMsg(r)
      \/ RMRcvAbortMsg(r) 


=============================================================================
\* Modification History
\* Last modified Thu Jan 18 22:13:56 CET 2024 by szsulik
\* Created Thu Jan 18 21:32:59 CET 2024 by szsulik
