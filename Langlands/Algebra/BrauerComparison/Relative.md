# The relative Brauer class of a matrix splitting

Let `L/K` be a field extension and let a supplied `L`-algebra equivalence identify
`L ⊗[K] A` with full matrices over `L` on a nonempty finite index type.
`relativeClass` uses the transported action on the actual matrix algebra. If
`P_s` is an invertible matrix lifting the linear part of the action of `s`, its
factor set is the unit whose scalar matrix is
`P_s s(P_t) P_(s*t)⁻¹`. The published matrix descent lemmas give scalarity and
the multiplicative cocycle identity. `unitClass` places this factor set in
Mathlib's ordinary degree-two cohomology of `Gal(L/K)` with coefficients in the
units of `L`. The additive wrapper turns multiplication of factors into
addition of classes and recognizes a zero class exactly by a unit coboundary.

Two lift families for one action differ pointwise by unit scalars. Comparing
their multiplication laws shows that the coboundary of this scalar ratio
relates the two factors. Two charts with the same indices differ by an inner
automorphism. Conjugating the chart by `U` replaces the lifts by
`U P_s s(U)⁻¹` and preserves their factors. These calculations prove
independence of the lifts and of the chart with those indices.

This realizes the descent convention in J.-P. Serre, *Local Fields* (1979),
Chapter X, §5, printed pp. 158–159, Proposition 8 and the factor-set formula in
the proof of Lemma 1. The cochain calculations implement that convention in
Mathlib's actual low-degree quotient. The constructions apply in every
characteristic, with `K`, `L`, and `A` in any common universe and the matrix
index type in an independent universe.
