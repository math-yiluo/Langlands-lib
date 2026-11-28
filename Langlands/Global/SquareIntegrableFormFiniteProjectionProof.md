# Finite-dimensional span of projections of square-integrable automorphic forms

`Langlands.Global.squareIntegrableFormFiniteProjection` proves
`Langlands.Global.SquareIntegrableFormFiniteProjectionStatement`. For a presented parabolic
isomorphic to the full group, the projections of the \(L^2([G])\) class of a finite linear
combination of square-integrable induced forms lie in one finite-dimensional subspace as the
closed invariant subspace varies. [Statement](AdelicGroupDiscreteSpectrumReduction.md)

The theorem applies `squareIntegrableFormFiniteProjection_of_reduction` to two inputs.

1. `parabolicLeviCenterRestriction` gives finite restriction of the archimedean enveloping
   centres. `arithmeticHarishChandraFiniteness_of_leviCenterRestriction` uses this comparison
   in the constant-term induction and passes the resulting rational adelic bound to the
   arithmetic quotients. `parabolicHarishChandraFiniteness_of_arithmetic_and_center` then uses
   the arithmetic bound and the same centre comparison to give fixed-type finiteness on the
   parabolic quotient. The proof uses these theorems at universe zero.
   [Centre restriction](../Automorphic/GroupSchemeLeviCenterRestrictionProof.md),
   [Arithmetic finiteness](../Automorphic/GroupSchemeArithmeticHarishChandraInduction.md),
   [Parabolic finiteness reduction](../Automorphic/GroupSchemeHarishChandraParabolicReduction.md)
2. `squareIntegrableProjectionAutomorphy` gives an automorphic representative of each
   projection with the same open finite level, cofinite centre ideal and space of
   archimedean compact profiles as the original combination.
   [Projection automorphy](AdelicSquareIntegrableProjectionAutomorphyProof.md)

The reduction identifies the left parabolic subgroup with \(G(F)\) in the full-group case and
derives invariance of the combination under the split centre \(A_G\). It fixes one type for the
combination and uses finiteness for the span of the automorphic functions of that type. The
linear map taking the square-integrable part of that span to \(L^2([G])\) has finite-dimensional
range. Every projected class belongs to that range by the representative theorem.
[Finite projection reduction](AdelicFiniteProjectionReduction.md)

The fixed-type finiteness step is the adelic form of Harish-Chandra's theorem in Borel–Jacquet,
*Automorphic forms and automorphic representations*, §4.3(i), printed p. 195. The representative
step uses Harish-Chandra's reproducing function as in Getz–Hahn, *An introduction to automorphic
representations*, Theorem 6.2.4 and the proof of Corollary 6.2.5, printed p. 160, and the
quotient convolution growth estimate from Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series*, I.2.4–I.2.5, printed pp. 25–27. The linked proofs give the source
locators and the details of their use in Lean.
