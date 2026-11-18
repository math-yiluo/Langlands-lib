# The coset sum of a fundamental weight over its simple-vertex field

This module specializes the coset sum of `StarFixedWeights` to the actual simple-vertex
field of a `TitsIndexData` (Task 7603, clause 4, lattice part).

## Setting

`K` is a field, `G` an affine, locally finite type group scheme over `Spec K` and
`d : TitsIndexData G` (Library). It provides the star action `d.star` of
`SeparableClosure K ≃ₐ[K] SeparableClosure K` on the simple vertices `d.Vertex`, the
pinning `d.pinning : GaloisPinningData K (SeparableClosure K) G`, the vertex stabilizer
`d.starVertexStabilizer a` and the simple-vertex field `d.starVertexField a`, the fixed
field of that stabilizer, with `d.starVertexField_fixingSubgroup` and
`d.finrank_starVertexField` (Library, `SimplyConnected/TypeD4CubicLeafField`). For
`hsc : IsSimplyConnected G`, `d.absoluteFundamentalCharacter hsc a` is the actual
integral fundamental weight of `a`: the element of the fundamental-weight basis of the
character lattice of `T_{K_s}` dual to the simple coroots (Library,
`SimplyConnected/TypeD4CentralCharacters`).

## Results

* `vertexStarAction`: the star action on vertices as a `MulAction`.
* `starVertexStabilizer_finiteIndex`: each vertex stabilizer has finite index, the size of
  the finite vertex orbit (`MulAction.index_stabilizer`).
* `finiteDimensional_starVertexField` (instance): the simple-vertex field is finite over
  `K`, since its degree is that index.
* `starAction_absoluteFundamentalCharacter`: the star action of `σ` maps `ϖ_a` to
  `ϖ_{σ ⋆ a}`. This is `Langlands.RootDatum.fundamentalWeightBasis_aut` applied to the star
  automorphism, which preserves the chosen base.
* `absoluteFundamentalCharacter_injective`: `a ↦ ϖ_a` is injective (it is a basis).
* Stabilizer comparison. `starAction_absoluteFundamentalCharacter_eq_iff`: `σ` fixes `ϖ_a`
  exactly when `σ ⋆ a = a`. `equivStabilizer_absoluteFundamentalCharacter`: the star
  stabilizer of the weight `ϖ_a` is `d.starVertexStabilizer a`.
  `starVertexField_fixingSubgroup_eq_equivStabilizer`: the subgroup fixing the vertex
  field is the stabilizer of `ϖ_a`. These are proved from the injectivity and the
  equivariance of `a ↦ ϖ_a`. No central character is involved, and no central-character
  stabilizer is identified with a vertex stabilizer.
* `absoluteFundamentalCharacter_mem_fixedWeights`: `ϖ_a` is fixed by the subgroup fixing
  the vertex field, so it is a valid input of the coset sum for that field.
* `range_starAction_absoluteFundamentalCharacter`: the star orbit of `ϖ_a` is the image
  of the vertex orbit `{b | ∃ σ, σ ⋆ a = b}` under `b ↦ ϖ_b`.
* `cosetSum_starVertexField`: the vertex-field specialization,

  `cosetSum d.pinning (starVertexField a) ϖ_a = ∑ᶠ b ∈ {b | ∃ σ, σ ⋆ a = b}, ϖ_b`.

  The coset sum of `ϖ_a` over the cosets of `Gal(K_s / K_a)` (`K_a` the simple-vertex
  field) is the sum of the actual fundamental weights over the full star orbit of `a`,
  each vertex once. Since `Gal(K_s/K_a)` is the stabilizer of `ϖ_a`, every multiplicity
  `[Stab(ϖ_a) : Gal(K_s/K_a)]` is `1`. The proof is `cosetSum_eq_finsum_orbit` followed by
  reindexing along the injective map `b ↦ ϖ_b` (`finsum_mem_image`).

The orbit is finite, so the `finsum` is a finite sum. The statement is in every
characteristic and needs no inner-type hypothesis: the vertex orbit may have several
elements.

## Provenance

Internal. These are deductions from the Library's fundamental-weight basis, its
covariance under based root-datum automorphisms and the Library's vertex-field stabilizer
theorem. In Tits (1971), Proposition 5.1, `Γ₁` is the stabilizer of an element `c₁` of
Tits' group `C*`. Here the coset sum is taken for the weight `ϖ_a` itself, whose stabilizer
is proved to be the vertex stabilizer, so the field is the simple-vertex field. The
stabilizer of the image of `ϖ_a` in a group of central characters can be larger. This
module makes no claim about it. The transfer identity for this field, which needs the
obstruction and the corestriction, is not in this module.
