# Overgroup normalizer factorization

This is an internal supporting derivation from the Library's normalizer
restriction and maximal-torus conjugacy results. It does not prove the
root-subset intersection statement. It isolates the conjugacy step that can
be applied once an appropriate overgroup and its normalization are established.

Let `j : H ⟶ G` be monic as a morphism of schemes over a field `k`, and let
`f : T.toGrp ⟶ H` be a maximal torus. Assume `MaximalToriAreConjugate H`.
The proposition `OvergroupNormalizerFactorizationStatement` says the
following. If a subgroup `A` of `G(k)` contains the image of `H(k)`, and a
point `n ∈ A` normalizes the subgroup functor represented by `j` after every
refinement of the base test scheme, then there are `p ∈ H(k)` and
`nT ∈ normalizerPoints (f ≫ j)` such that `nT ∈ A` and
`n = j(p) * nT`. The theorem `overgroupNormalizerFactorization` proves this
proposition. The monomorphism assumption is on `j.hom.hom` in the category
of schemes over `Spec k`.

The proof of `exists_overgroup_mul_normalizerPoint` first restricts
conjugation by `n` to an automorphism `σ` of `H`, using
`SubgroupFunctor.normalizerRestrictionIso`. Maximal-torus conjugacy applied
to `f ≫ σ.hom` and `f` supplies `p₀ ∈ H(k)` and a torus automorphism.
Naturality of inner conjugation then shows that `j(p₀) * n` normalizes
`f ≫ j`. Taking `p = p₀⁻¹` gives the stated factorization. The torus
automorphism is converted from an isomorphism of group schemes to one of
commutative group schemes, as required by `normalizerPoints`.

The theorem `exists_overgroup_mul_normalizerPoint_mem` retains membership
in `A`: both `j(p)` and `n` belong to `A`, so `nT = j(p)⁻¹ * n` does too.
The corollary `pointSubgroup_le_range_of_normalizer_inter_le` concludes
`A ≤ j(H(k))` when every point of `A` normalizes `j` on all tests and
`A ⊓ normalizerPoints (f ≫ j) ≤ j(H(k))`. It applies the factorization
and multiplies two points of `j(H(k))`.

Finally, `exists_overgroup_mul_normalizerPoint_mem_of_isAlgClosed`
discharges the conjugacy premise using the published
`maximalTorusConjugacy` theorem when `k` is algebraically closed and `H`
is smooth, affine and connected. It imposes no such geometric assumptions
on `G`. All factorization conclusions concern points over `k`; the
normalization hypothesis still tests the subgroup functor over every
refinement. No assertion about an intersection's neutral component,
smoothness, maximal rank or Weyl-group membership is included here.
