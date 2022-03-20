# Isabelle and MetiTraski Code for Controller Verification of an Attitude Controller for Multirotor UAVs
## Paper title: Verification Framework for Control Theory of Aircraft

This repository contains the Isabelle and MetiTarski codes to illistrate the use of 
formal computer based techniques to verify 

(1) the control theory and

(2) realtime testing of stability onboard, 

both of which support support the safe operation of an unmanned multi-rotor aircraft. 

Extensive  mathematical derivations, which have formerly been carried out manually, 
are checked for their correctness by use of the Isabelle code. Higher-order logic 
interactive theorem-provers and an automated theorem-provers are to be used when 
this code is run.  

# The code files
  * The file "IsabelleHOL code/Quadrotor_Veri.thy" includes controller verification code of Isabelle/HOL.
  * The files "MetiTarski code/Stability_Eq47.tptp" and "MetiTarski code/Stability_Eq49.tptp" include stability testing code of MetiTarski.
  * The files "MetiTarski code/Proofs/Stability_Eq47.tstp" and "MetiTarski code/Proofs/Stability_Eq49.tstp" include the proofs of codes implemented in MetiTarski.



# Related publications

* O. A. Jasim, S. M. Veres, Towards formal proofs of feedback control theory, in: 2017 21st International Conference on System Theory, Control and Computing (ICSTCC), 2017, pp. 43-48. IEEE. https://doi.org/10.1109/ICSTCC.2017.8107009. 
* O. A. Jasim, S. M. Veres, Nonlinear Attitude Control Design and Verification for a Safe Flight of a Small-Scale Unmanned Helicopter. In 2019 6th International Conference on Control, Decision and Information Technologies (CoDIT) (pp. 1652-1657). IEEE. https://doi.org/10.1109/CoDIT.2019.8820310
* O. A. Jasim, S. M. Veres, A robust controller for multi rotor uavs, Aerospace Science and Technology, (2020). https://doi.org/10.1016/j.ast.2020.106010.

