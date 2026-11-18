# Adic separation for submodules supported on a closed locus

Worker 801 supplies an internal algebraic form of the last step in SGA 3,
Exposé IX, Lemma 6.2 (registered source `sga3-expose-ix-gille-polo-2009`, printed
p.54, retained PDF p.24). The source separates a finite-length ideal from a
sufficiently deep power of the maximal ideal. The implemented argument instead
uses support and Artin–Rees, so it needs no local-ring or finite-length
hypothesis.

Let `R` be a noetherian commutative ring, `M` a finite `R`-module, `N` a submodule
and `J` an ideal. If `J^e N = 0` for some `e`, Artin–Rees gives a positive `n`
with `N ∩ J^(n+1)M = 0`. More generally, support of `N` in the closed locus
`V(J)` implies that `J` lies in the radical of the annihilator of `N`.
Finite generation of `J` then supplies such an annihilating power. The internal
integer construction `separationIndex` chooses a positive separating stage,
with its positivity and intersection property proved.

The subsequent criteria say that if `P ⊆ N` has zero image modulo the separating
power, then `P = 0`. Ideal versions specialize to `M = R`. In the exhaustion
argument `N` represents an earlier defining ideal and `P` a later, smaller
ideal. A statement that only the earlier ideal vanished modulo the chosen power
would not express the required index increase; the criteria retain both ideals.

This module contains the algebraic separation step. It does not assert the
geometric exhaustion theorem or the global uniform exponent theorem.
