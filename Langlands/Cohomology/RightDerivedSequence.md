# Long exact sequence of right derived functors

Author: Worker 61. This module is derived infrastructure. It imports
`Langlands.Cohomology.DerivedPlusNaturality` and Mathlib's
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.

## Setting

`F : C ⥤ D` is an additive functor between abelian categories, and `C` has
enough injectives. Derived categories are chosen by
`[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{w'} D]`, and all
universes are independent, as in `Langlands.Cohomology.DerivedPlus`. `S` is a
short complex in `C` and `hS : S.ShortExact`, so
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` is exact. `F` is not assumed left exact. The
classical right derived functors are Mathlib's `F.rightDerived n`.

## The triangle in the bounded below derived category

Mathlib's `hS.singleTriangle` is a distinguished triangle in `DerivedCategory C`.
Its objects are `S.X₁`, `S.X₂` and `S.X₃` placed in degree zero. Its third map
is Mathlib's connecting morphism `hS.singleδ`, built from the mapping cone of
`S.f`. `DerivedCategory.Plus C` is Mathlib's full triangulated subcategory of
bounded below objects. Its distinguished triangles are those whose image under
the inclusion `DerivedCategory.Plus.ι` is distinguished.

- `singleδPlus hS` is the morphism of `DerivedCategory.Plus C` whose image
  under the fully faithful inclusion is `hS.singleδ`, followed by the
  inclusion's shift comparison `(ι.commShiftIso 1).inv`.
  `ι_map_singleδPlus` records this image.
- `singleTrianglePlus hS` is the triangle with maps
  `(DerivedCategory.Plus.singleFunctor C 0).map S.f`, the same functor applied
  to `S.g`, and `singleδPlus hS`.
- `ιMapSingleTrianglePlusIso hS` identifies its image under the inclusion with
  `hS.singleTriangle`. All three components are identities.
  `singleTrianglePlus_distinguished` follows from Mathlib's
  `singleTriangle_distinguished`.
- `singleδPlus_naturality` and `singleTrianglePlusMap h₁ h₂ φ` give the
  morphism of triangles induced by a morphism `φ : S₁ ⟶ S₂` of short exact
  sequences. The proof is through the faithful inclusion and Mathlib's
  `ShortComplex.ShortExact.singleTriangle.map`.

## Cohomology of derived complexes

- `derivedTriangle F hS` is the image of `singleTrianglePlus hS` under
  `F.rightDerivedFunctorPlus` and then the inclusion into `DerivedCategory D`.
  Its objects are the derived complexes `(derivedComplex F).obj S.Xᵢ`.
  `derivedTriangle_distinguished` holds because Mathlib's
  `F.rightDerivedFunctorPlus` is triangulated.
- For `n₀ n₁ : ℤ` with `n₀ + 1 = n₁`, `derivedδ F hS n₀ n₁ h` is Mathlib's
  connecting morphism `DerivedCategory.HomologySequence.δ` of this triangle.
  Its source and target are written with the functors
  `derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n`.
- `derived_map_comp_map`, `derived_map_comp_δ` and `derivedδ_comp_map` say
  that consecutive maps compose to zero. `derived_exact₂`, `derived_exact₃`
  and `derived_exact₁` give exactness at the terms of `S.X₂`, `S.X₃` and
  `S.X₁`. They are Mathlib's `HomologySequence` lemmas for the distinguished
  triangle.
- `derivedδ_naturality` is naturality in morphisms of short exact sequences.
  It is Mathlib's `homologySequenceδ_naturality` applied to the image of
  `singleTrianglePlusMap`.

## Right derived functors

- For `n₀ n₁ : ℕ` with `n₀ + 1 = n₁`, `rightDerivedδ F hS n₀ n₁ h` is the
  morphism `(F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁`.
  It is `derivedδ` conjugated by the components of the natural isomorphism
  `homologyNatIso F n` of `Langlands.Cohomology.DerivedPlusNaturality`.
  `homologyNatIso_hom_app_comp_rightDerivedδ` records the compatibility.
- `rightDerived_map_zero` says that `F.rightDerived n` sends zero morphisms to
  zero. Mathlib provides no additivity instance for `F.rightDerived n`. The
  lemma is proved with Mathlib's `Functor.rightDerived_map_eq`, applied to the
  zero cochain map between chosen injective resolutions.
- `rightDerived_map_comp_map`, `rightDerived_map_comp_δ` and
  `rightDerivedδ_comp_map` say that consecutive maps compose to zero.
- `rightDerived_exact₂`, `rightDerived_exact₃` and `rightDerived_exact₁` are
  exactness of
  `R^n F(S.X₁) ⟶ R^n F(S.X₂) ⟶ R^n F(S.X₃)`,
  `R^n₀ F(S.X₂) ⟶ R^n₀ F(S.X₃) ⟶ R^n₁ F(S.X₁)` and
  `R^n₀ F(S.X₃) ⟶ R^n₁ F(S.X₁) ⟶ R^n₁ F(S.X₂)`.
  Each is the corresponding derived statement, transported along an
  isomorphism of short complexes built from `homologyNatIso`.
- `mono_rightDerived_zero_map` says that `(F.rightDerived 0).map S.f` is a
  monomorphism. The derived complex of `S.X₃` has zero cohomology in degree
  `-1`, by `isZero_homology_of_neg` of `Langlands.Cohomology.DerivedPlus`. So
  the connecting morphism from degree `-1` vanishes, and Mathlib's
  `mono_homologyMap_mor₁_iff` applies.
- `epi_rightDerivedδ_of_isZero`, `mono_rightDerivedδ_of_isZero` and
  `isIso_rightDerivedδ_of_isZero` say that `rightDerivedδ F hS n₀ n₁ h` is an
  epimorphism if `R^n₁ F(S.X₂)` is zero, and a monomorphism if `R^n₀ F(S.X₂)` is
  zero. It is an isomorphism if both are zero. These are the steps used in
  dimension shifting.
- `epi_rightDerived_zero_map_of_isZero` says that `(F.rightDerived 0).map S.g`
  is an epimorphism if `R^1 F(S.X₁)` is zero, by exactness at `R^0 F(S.X₃)`.
- `shortExact_map_of_isZero_rightDerived_one` assumes in addition that `F`
  preserves finite limits. If `R^1 F(S.X₁)` is zero, then `S.map F` is short
  exact. The sequence of degree-zero derived functors is short exact by the
  three previous facts. It is transported along Mathlib's
  `Functor.rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F` and its naturality.
- `rightDerivedδ_naturality` says that for a morphism `φ : S₁ ⟶ S₂` of short
  exact sequences,
  `rightDerivedδ F h₁ n₀ n₁ h ≫ (F.rightDerived n₁).map φ.τ₁ =
  (F.rightDerived n₀).map φ.τ₃ ≫ rightDerivedδ F h₂ n₀ n₁ h`.

Exactly eight lemmas carry `@[reassoc]`: `singleδPlus_naturality`,
`derivedδ_naturality`, `rightDerivedδ_naturality`,
`homologyNatIso_hom_app_comp_rightDerivedδ`, `derived_map_comp_δ`,
`derivedδ_comp_map`, `rightDerived_map_comp_δ` and `rightDerivedδ_comp_map`.

## Provenance and scope

Cartan and Eilenberg, *Homological Algebra* (1956), Chapter V, Section 4
(printed pp. 84-86), define connecting homomorphisms
`R^n T(A'') ⟶ R^(n+1) T(A')` for an exact sequence `0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0`.
Their Proposition 4.1 (printed p. 85) proves naturality in commutative
diagrams of exact sequences and exactness of the sequence
`⋯ ⟶ R^n T(A') ⟶ R^n T(A) ⟶ R^n T(A'') ⟶ R^(n+1) T(A') ⟶ ⋯`.
Their Corollary 4.2 (printed p. 86) states that `R^0 T` is left exact, and
that `R^n T` is right exact if `R^(n+1) T = 0`.
Grothendieck, *Sur quelques points d'algèbre homologique* (Tôhoku 1957),
Section 2.3 (printed p. 143), transfers Cartan-Eilenberg Chapter V to abelian
categories. This module proves these properties for a single covariant
additive functor `F` on an abelian category with enough injectives. Left
exactness of `R^0 F` is `mono_rightDerived_zero_map` together with
`rightDerived_exact₂` in degree zero. Corollary 4.2 also states that `R^n T`
is right exact when `R^(n+1) T = 0`. `epi_rightDerived_zero_map_of_isZero` is
the case `n = 0` for a single sequence, assuming only `R^1 F(S.X₁) = 0`.
`shortExact_map_of_isZero_rightDerived_one` combines it with left exactness.

The connecting morphism is constructed differently. Cartan and Eilenberg take
the homology sequence of `T` applied to an injective resolution of the exact
sequence. Here it comes from Mathlib's mapping-cone triangle in the derived
category, through `F.rightDerivedFunctorPlus` and `homologyNatIso`. This module
does not compare `rightDerivedδ` with the Cartan-Eilenberg morphism, and it
makes no claim about their relative sign. Mathlib has no horseshoe
construction for `F.rightDerived`. Exactness, naturality and the criteria above
do not depend on that comparison.

Its purpose in the Harris framework is the comparison of acyclic resolutions
with right derived functors: Worker 3's
`Langlands.Cohomology.AcyclicResolutionComparisonStatement`. That statement is
not proved here.

Not provided: a comparison with the Cartan-Eilenberg connecting morphism,
contravariant or multi-variable functors, and the long exact sequence for
short exact sequences of complexes.
