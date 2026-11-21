# Polynomial counting in a product with one compact slice

`Langlands.Analysis.DiscreteProductSubgroupCountingStatement` and its proof
`discreteProductSubgroupCounting` concern a discrete additive subgroup Γ of `E × A`,
where `E` is a finite-dimensional real normed vector space and `A` a Hausdorff
commutative topological group written additively. For every compact set `C ⊆ A`,
there is a nonnegative real constant `B` such that for every `R ≥ 0`,

\[
P_R=\Gamma\cap(\overline B_E(0,R)\times C)
\]

is finite and \(\#P_R\le B(1+R)^{\dim_{\mathbb R} E}\). Finiteness is a separate
conclusion, since `Set.ncard` alone does not express it. There is no cocompactness
hypothesis and no local compactness hypothesis on `A`.

## Implemented proof

Discreteness gives a product neighborhood of zero isolating zero in Γ. Shrink its
first factor to a ball of positive radius `r`. Choose an open zero neighborhood
`O` in the second factor such that differences of elements of `O` lie in the
second factor of the isolating neighborhood. A finite number of translates of
`O` cover `C`. Inside a single translate, distinct points of `P_R` have first
coordinates at distance at least `r`, since otherwise their difference would be a
nonzero element of Γ in the isolating neighborhood.

The proof first obtains finiteness of `P_R` from compactness of the closed ball
and `C`, and closedness and discreteness of Γ. On each piece of the cover it fits
pairwise disjoint open balls of radius `ε = r / 2`, centered at the first
coordinates, inside the open ball of radius `R + ε`. Translation invariance and
scaling of additive Haar measure bound the cardinality of the piece by
`((R + ε) / ε)^d`, where `d = Module.finrank ℝ E`. Here the common measure of the
unit ball is positive and finite, so it can be cancelled. Since
`(R + ε) / ε ≤ (max 1 ε / ε) * (1 + R)`, the cardinality bound follows by summing
over the finite cover; its translates need not be disjoint.

## Provenance and scope

This is a derived packing estimate for the growth step in the route from a
cuspidal Hilbert summand to automorphic forms. The disjoint-ball proof adapts
Mathlib's `Besicovitch.card_le_of_separated` (in
`Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`), which uses fixed
radii. The compact-slice argument is the additional product step. This module
neither identifies the discrete subgroup of rational matrices in the adeles nor
bounds a quotient convolution; those require the adelic specialization.
