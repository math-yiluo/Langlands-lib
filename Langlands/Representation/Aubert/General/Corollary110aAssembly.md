# Assembly of Corollary 1.10(a)

Authors: Worker 1343; the imported inside-Levi eigenvalue proof is by Worker 1254.

This internal proof adapter is conditional on the published proposition
`InductionCompatibilityStatement` and the actual inside-Levi finite-length
packages. It does not prove those inputs or the exact rational-point corollary.
The final rational-point proof must discharge them from its visible premises and
published proofs.

Evaluate the equality of linear maps expressing induction compatibility at the
actual finite-length class of the cuspidal representation. The theorem
`leviAlternatingOperator_ofObject_of_isCorollaryLeviCuspidal` computes the
inside-Levi operator at that class as multiplication by `(-1)^|J|`.
Integer linearity of actual induction on the exact Grothendieck group then
gives the required induced eigenvalue. The irreducibility assumptions from
`corollary110a` remain quantified, although this argument proves the equality
without using them. Every subset, including the empty set, is treated by the
same argument.

The implemented assembly uses only `LinearMap.congr_fun`, the imported
inside-Levi eigenvalue theorem, and `map_smul`. Representation-theoretic inputs
to induction compatibility remain explicit and require their own proof audit.
