# Transfer of facet incidence along an affine map preserving facets

Module `Langlands.Geometry.Building.AffineFacetIncidenceTransfer`.

## Setting

`A` and `A₂` are real affine spaces over the real vector spaces `V` and `V₂`.
`Ψ` and `Ψ₂` are sets of affine functions `A → ℝ` and `A₂ → ℝ`. The facets,
facet closures and the face relation are the Library's
(`Langlands/Geometry/Building/AffineRootSystem.lean`):

- `facet Ψ x` is the set of `y` with `sign ψ(y) = sign ψ(x)` for every
  `ψ ∈ Ψ`;
- `facetClosure Ψ x` is the set of `y` with `sign ψ(y) = 0` or
  `sign ψ(y) = sign ψ(x)` for every `ψ ∈ Ψ`;
- `IsFaceOf Ψ F' F` means that `F'` is a facet and `F = facet Ψ x` for some
  `x` with `F' ⊆ facetClosure Ψ x`.

`a : A →ᵃ[ℝ] A₂` is an affine map with the facet hypothesis

`ha : ∀ w, a ⁻¹' facet Ψ₂ (a w) = facet Ψ w`.

This is hypothesis 7 of the Library statement
`UnramifiedFacetCommonTorusStatement`, with `Ψ` the affine roots of the
apartment of the valuation building data of `G` over `F` and `Ψ₂` the affine
roots of the apartment of the building data over the maximal unramified
extension.

## Content

- `lineMap_mem_facet_of_mem_facetClosure`: if `y ∈ facetClosure Ψ x` and `0 < t ≤ 1`, then
  `lineMap y x t = y + t (x - y)` lies in `facet Ψ x`.
- `sign_eq_zero_or_eq_of_lineMap`: for one affine function `ψ`, if
  `sign ψ(lineMap y x t) = sign ψ(x)` for every `0 < t ≤ 1`, then
  `sign ψ(y) = 0` or `sign ψ(y) = sign ψ(x)`.
- `map_mem_facetClosure`: under `ha`, if `y ∈ facetClosure Ψ x` then
  `a y ∈ facetClosure Ψ₂ (a x)`.
- `exists_isFaceOf_image`: under `ha`, if `Fa` is a face of `Fa'` for `Ψ`
  and `x ∈ Fa`, there is `x₁` with `facet Ψ x₁ = Fa'` such that
  `facet Ψ₂ (a x)` is a face of `facet Ψ₂ (a x₁)` for `Ψ₂`,
  `a '' Fa ⊆ facet Ψ₂ (a x)` and `a '' Fa' ⊆ facet Ψ₂ (a x₁)`.

## Proofs

`lineMap_mem_facet_of_mem_facetClosure`. The value of `ψ` at `lineMap y x t` is
`(1 - t) ψ(y) + t ψ(x)`. If `ψ(x) < 0`, then `ψ(y) ≤ 0` because `y` is in
the facet closure, so the value is negative. If `ψ(x) = 0`, then `ψ(y) = 0`
and the value is `0`. If `ψ(x) > 0` the argument is symmetric.

`sign_eq_zero_or_eq_of_lineMap`. Suppose `ψ(y) ≠ 0` and
`sign ψ(y) ≠ sign ψ(x)`. If `ψ(x) = 0`, the hypothesis at `t = 1/2` gives
`ψ(y)/2 = 0`, a contradiction. Otherwise `ψ(y)` and `ψ(x)` have opposite
signs, and `t = ψ(y) / (ψ(y) - ψ(x))` lies in `(0, 1]` with
`ψ(lineMap y x t) = 0`. The hypothesis at this `t` then gives `ψ(x) = 0`, a
contradiction.

`map_mem_facetClosure`. For `0 < t ≤ 1` the point `lineMap y x t` lies in
`facet Ψ x` (`lineMap_mem_facet_of_mem_facetClosure`), hence in `a ⁻¹' facet Ψ₂ (a x)` by `ha`.
Since `a` commutes with `lineMap`, every `ψ ∈ Ψ₂` has the sign of `ψ(a x)` on
the half-open segment from `a y` to `a x`, and
`sign_eq_zero_or_eq_of_lineMap` applies.

`exists_isFaceOf_image`. Write `Fa = facet Ψ x₀`, `Fa' = facet Ψ x₁` with
`Fa ⊆ facetClosure Ψ x₁`. Since `x ∈ Fa`, `Fa = facet Ψ x`. By
`map_mem_facetClosure`, `a x ∈ facetClosure Ψ₂ (a x₁)`, so
`facet Ψ₂ (a x) ⊆ facetClosure Ψ₂ (a x₁)` (Library lemma
`facet_subset_facetClosure_iff`). The two image inclusions are `ha` at `x`
and at `x₁`.

## Provenance

The facet, facet-closure and face definitions follow Kaletha–Prasad, Remark
1.3.16 and the 2024 corrections to Proposition 1.3.35 (via the Library
definitions). The lemmas here are elementary consequences of these
definitions; they are internal infrastructure for the proof of
`UnramifiedFacetCommonTorusStatement` and are not taken from the literature.

The segment lemma is imported from [FacetClosurePullback](FacetClosurePullback.md).
