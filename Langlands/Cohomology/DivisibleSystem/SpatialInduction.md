# ℓ-divisible systems under equivalences and spatial induction

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem`: `ℓ`-divisible systems (Harris 1999,
  (2.1)), `hom_ext`, `mapFunctor C ℓ F` for exact additive functors, and
  `SmoothSheafDivisibleSystem R G X ℓ`.
- Worker 13's `Langlands.Sheaf.Equivariant.SmoothSpatialInduction`: the
  equivalence `SpatialInduction.smoothRestrictionEquivalence R H hH X` between
  `G`-equivariant smooth sheaves on the induced space `Space H X` (written
  `G ×ᴴ X` below) and `H`-equivariant smooth sheaves on `X`. Its functor is
  restriction to the unit chart, `smoothRestrict R H hH X`, and its inverse is
  smooth spatial induction, `smoothInduce R H hH X`.
- `Langlands.Sheaf.Equivariant.SmoothSpatialLocallyConstant`:
  `SpatialInduction.hasStableNeighbourhoods_induced H hH X`, which builds
  stable neighbourhoods on `G ×ᴴ X` from stable neighbourhoods on `X`.

All names below are in the namespace `Langlands.Cohomology.DivisibleSystem`.
For a system `T`, write `T m` for `T.tower.obj m` and `i` for the inclusions
`T.inclusion h : T m' ⟶ T m` (`m' < m`), as in the parent module.

## Equivalences of abelian categories

`C` and `D` are abelian categories.

- `isoMk e he`: an isomorphism `T ≅ T'` of `ℓ`-divisible systems, built from an
  isomorphism `e : T.tower ≅ T'.tower` of the underlying inverse systems and
  the equations `he` saying that `e.hom` commutes with the inclusions `i`.
  The inverse commutes with the inclusions because `e.hom` is levelwise an
  isomorphism. `@[simps]` records `hom` and `inv`.
- `mapFunctor_map_tower F f`: the components of `(mapFunctor C ℓ F).map f`
  are `F` applied to the components of `f` (`rfl`).
- `equivalence_functor_additive e`: the functor of an equivalence
  `e : C ≌ D` of abelian categories is additive. Proof: it preserves binary
  products (Mathlib's `Functor.additive_of_preserves_binary_products`). The
  inverse is then additive by Mathlib's `Equivalence.inverse_additive`. Both
  functors preserve all finite limits and colimits, as equivalences.
- `mapEquivalence ℓ e : DivisibleSystem C ℓ ≌ DivisibleSystem D ℓ`. The functor
  is `mapFunctor C ℓ e.functor` and the inverse is `mapFunctor D ℓ e.inverse`
  (`mapEquivalence_functor`, `mapEquivalence_inverse` by `@[simps]`). The
  unit and counit are built with `isoMk` from the whiskered unit and counit of
  `e`. They commute with the inclusions by naturality of the unit and counit
  of `e`. The triangle identity holds levelwise by `e.functor_unit_comp`.
- `mapEquivalence_unitIso_hom_app_tower_app` and the `_unitIso_inv_`,
  `_counitIso_hom_` and `_counitIso_inv_` variants: the components of the unit
  and counit at level `m` are those of `e` at `T m` (`rfl`).

## Spatial induction

`R` is a commutative ring, `G` is a topological group, `H` is a subgroup of
`G` with `hH : IsOpen (H : Set G)`, and `X` is a topological space with a
continuous `H`-action and `HasStableNeighbourhoods H X`. `R`, `G` and `X` lie
in one universe, as in `SmoothSpatialInduction`.

- `smoothRestrictionSystemEquivalence R H hH X ℓ` is
  `mapEquivalence ℓ (SpatialInduction.smoothRestrictionEquivalence R H hH X)`.
  It is an equivalence between `SmoothSheafDivisibleSystem R G (Space H X) ℓ`
  and `SmoothSheafDivisibleSystem R H X ℓ`. The abelian structure on smooth
  sheaves on `G ×ᴴ X` uses the stable neighbourhoods
  `hasStableNeighbourhoods_induced H hH X`. It is supplied by `letI` in the
  statement, so no second stable-neighbourhood hypothesis is assumed. The
  Library does the same, for example in
  `OpenSubgroupTransport.SpatialSheaves.smoothCohomologySheafFunctorIso` of
  `Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothSpatialSheaves`.
- `smoothRestrictionSystemEquivalence_functor_obj_tower`: the functor sends a
  system `T` on `G ×ᴴ X` to the system with tower
  `T.tower ⋙ smoothRestrict R H hH X` (`rfl`).
- `smoothRestrictionSystemEquivalence_inverse_obj_tower`: the inverse sends a
  system `T` on `X` to the system with tower `T.tower ⋙ smoothInduce R H hH X`
  (`rfl`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.303–304 (one-based PDF
pages 5–6). Worker 61 read both pages in the rendered scan.

1. What Harris uses. On p.303 Harris writes: "Recall that the action of GJ on
   Ω lifts to an action on 𝓜̆_N, and U(ẽ) is stabilized by a compact open
   subgroup S(ẽ) ⊂ GJ." On p.304 he defines: "By an ℓ-divisible system of
   S(ẽ)-modules over U(ẽ) we mean a collection {T_m} of étale sheaves in
   smooth ℤ/ℓ^mℤ[S(ẽ)]-modules over U(ẽ)", subject to (2.1). So his local
   systems are equivariant only for the open subgroup `S(ẽ)` stabilizing
   `U(ẽ)`, while `GJ` acts on the whole space.
2. What is formalized. The module is internal framework. Harris does not
   state the induction equivalence. The construction `G ×ᴴ X` is the
   Library's induced space (Worker 13). Reading `H` as `S(ẽ)` and `X` as
   `U(ẽ)` is our interpretation. Under it, the module identifies
   `ℓ`-divisible systems of `S(ẽ)`-equivariant smooth sheaves on `U(ẽ)` with
   `ℓ`-divisible systems of `GJ`-equivariant smooth sheaves on the induced
   space `GJ ×^{S(ẽ)} U(ẽ)`. The general part, `mapEquivalence`, is a
   standard fact: an equivalence of abelian categories is exact, so it
   preserves the conditions defining `ℓ`-divisible systems.
3. Sites. As in the parent module, the Library's sheaves are equivariant
   sheaves on topological spaces with ordinary opens, not étale sheaves on
   rigid analytic spaces. The induced space `G ×ᴴ X` is a topological space.
   It is not identified here with an open subspace of Harris's 𝓜̆_N, such as
   the union of the `GJ`-translates of `U(ẽ)`.

## Scope

The module makes no statement about cohomology or compact sections of the
systems. It does not compare the induced space with any subspace of a
Drinfeld space or of 𝓜̆_N. It does not include the specialization to the
rational spectra of `Langlands.Geometry.Analytic.StrictTestDomain`, where the
Library's `OpenSubgroupTransport.SpatialSheaves.smoothRestrictionEquivalence`
is also defined from `SpatialInduction.smoothRestrictionEquivalence`; that
would add a dependency on the analytic geometry modules.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
