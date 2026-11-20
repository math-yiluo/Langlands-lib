# Transposition of conjugation-invariant real general linear distributions

This statement specializes Aizenbud and Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, arXiv:0803.3395v7, Corollary 7.6.3, p. 22, to `GL_(r+1)(ℝ)` for every natural number `r`. Its conclusion is invariance of any conjugation-invariant distribution under ordinary matrix transposition. Both invariance predicates use the bundled pullbacks of the real smooth compactly supported tests.

The invertible real matrices are an open subset of the real matrix space and give the usual smooth coordinates on the real general linear group. Mathlib models complex-valued distributions as continuous real-linear functionals on real scalar tests. The corresponding complex functional on complex tests is determined by real and imaginary parts. The two pullbacks extend by the same rule, so testing invariance on real scalar tests gives the source's condition.

The proposition is the distributional input of the trace-character route to Task 7534. Theorem 8.2.1, p. 23 of the same source, uses Corollary 7.6.3 for the comparison between the smooth contragredient and the inverse-transpose twist.
