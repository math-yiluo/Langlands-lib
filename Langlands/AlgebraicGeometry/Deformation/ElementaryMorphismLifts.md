# Ordinary morphism lifts with a group on the residue fibre

Let `R` be a local ring with maximal ideal `m` and let `I` be a proper ideal
with `mI = 0`. The target is a scheme over `Spec R` with a group law on its
residue fibre. Two maps from `Spec C` over `Spec R` with the same restriction
to `Spec(C/IC)` determine a split infinitesimal point of the residue group.
Translate this point by the inverse of the constant extension of its
reduction to obtain a split point at the identity. Given an affine
neighbourhood of the identity, the split point gives a linear map from the
cotangent space there to the coefficient ideal. Multiplication by the
constant extension reverses the translation, and the affine pushout
recovers the corresponding corrected lift.

This gives the affine comparison in SGA 1, Exposé III, Proposition 5.1,
specialized using the group translation of SGA 3, Exposé III, Remarque 0.4.

Smoothness of the target over `Spec R` supplies lifts on affine tests. The
triple comparison, followed by translation by the common constant point,
identifies the total difference with the sum of successive differences on
each cotangent vector.

For the scalar coordinates, take `C` flat over `R` and choose finite bases
over `R/m` of the cotangent space and of `I`. The coordinates lie in `C/mC`
and are indexed by pairs of basis elements. `Coordinates.ofTarget` supplies
these choices when `R` is Artinian and the residue group is smooth.
The coordinates commute with every map of flat tests. Taking the difference
from a fixed lift and correcting that lift by prescribed coordinates are
inverse operations. A zero difference implies equality when the two maps
have the same reduction.

Sources are `sga1-arxiv-math-0206203v2`, Exposé III, Proposition 5.1 and
Corollaire 5.2, printed pp. 59–61 (PDF pp. 75–77), SHA-256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`, and
`sga3-expose-iii-gille-polo-2024`, Exposé III, Remarques 0.3–0.4, printed
p. 114 (PDF p. 14), SHA-256
`b799de7ca975b738bdc293d703c257e63caffd6fa9365f5a398d6e01cb9599e6`.
