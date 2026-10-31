# Integral identities for rank-one gamma twists

Worker 458. This internal helper compares the actual forward and dual
coefficient products, then passes those comparisons through the total Bochner
integrals. Every unequal-rank rectangular block and every equal-rank
Schwartz--Bruhat function is retained. The dual unequal-rank identity uses the
actual right translation by the block Weyl matrix and has multiplier
`χ(-1)^n`. The equal-rank identities specialize to candidate and test rank one.
The provenance is the JPSS definitions detailed in the statement companion and
the determinant calculation in `RankOneGammaTwistAlgebra`; no convergence or
analytic existence theorem is used.
