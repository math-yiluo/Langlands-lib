# Identity and composition for actual bounded-below geometric pullback

This module constructs the geometric inverse-image identity and composition
isomorphisms on bounded-below cochain complexes, and proves the corresponding
laws for the existing actual section-complex pullback.

## Parameters and scope

Let `X`, `Z`, and `V` belong to `Scheme.{u}`, let `f : Z ⟶ X` and
`g : V ⟶ Z` be arbitrary scheme morphisms, and let `R : Type u` be a
commutative ring. The coefficient category is `ModuleCat.{u} R`, and
`ModuleSheaf X R` is the category of actual module-valued sheaves on
`X.smallEtaleTopology`.

Write `L_f = EtaleInverseImage.inverseImage f R`, `Γ_X =
EtaleDerivedSections.sections X R`, and `C⁺(F) = F.mapCochainComplexPlus`.
The superscript means the actual full subcategory of bounded-below cochain
complexes with integer degrees. These constructions require no chosen derived
categories or localization universes. No etaleness, flatness, affineness,
finiteness or Noetherian assumption on either morphism is imposed.

## Inverse-image comparisons on complexes

`EtaleInverseImage.inverseImageComplexId R X` constructs

```text
C⁺(L_id) ≅ 𝟭 (CochainComplex.Plus (ModuleSheaf X R)).
```

Its underlying unbounded-complex comparison is
`NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ)` followed by
`Functor.mapHomologicalComplexIdIso`. It is lifted through the fully faithful
inclusion of bounded-below complexes using `preimageIso`. Naturality follows
from the original natural isomorphism after applying that faithful inclusion.
`inverseImageComplexId_hom_f` proves that its forward map in every degree `i`
is exactly `(inverseImageId R X).hom.app (K.obj.X i)`.

`EtaleInverseImage.inverseImageComplexComp R f g` constructs

```text
C⁺(L_f) ⋙ C⁺(L_g) ≅ C⁺(L_(g≫f)).
```

Its underlying comparison is the original
`Functor.mapHomologicalComplexCompIso (inverseImageComp R f g) (.up ℤ)`,
lifted through the same fully faithful bounded-below inclusion. Again its
naturality is the naturality of that actual comparison.
`inverseImageComplexComp_hom_f` identifies its forward component in degree
`i` with `(inverseImageComp R f g).hom.app (K.obj.X i)`.

Thus both comparisons use the existing ordinary inverse-image isomorphisms,
which are determined by the actual geometric adjunctions. No arbitrary
comparison is supplied as a parameter. Their termwise maps commute with the
actual differentials by the original natural-isomorphism construction.

## Section-complex laws

Write `s⁺_f = EtaleDerivedGlobalPullback.sectionsComplexPullback f R`.
This is the existing map `C⁺(Γ_X) ⟶ C⁺(L_f) ⋙ C⁺(Γ_Z)` defined by the
actual complex adjunction unit and the terminal/global-section comparison.
For each bounded-below complex `K`, `sectionsComplexPullback_id` proves

```text
s⁺_id.app K ≫ C⁺(Γ_X).map (inverseImageComplexId.hom.app K) = 𝟙 _.
```

`sectionsComplexPullback_comp` proves

```text
s⁺_f.app K ≫ s⁺_g.app (C⁺(L_f).obj K)
  ≫ C⁺(Γ_V).map (inverseImageComplexComp.hom.app K)
  = s⁺_(g≫f).app K.
```

Both proofs first apply the faithful inclusion into all cochain complexes and
then use equality of complex maps degree by degree. The published
`sectionsComplexPullback_app_f` identifies each section-map component with the
existing ordinary `sectionsPullback`. The two component lemmas above identify
the coefficient-comparison maps. The remaining equalities are precisely
`sectionsPullback_id` and `sectionsPullback_comp` from
`EtaleSectionPullbackCoherence`. Consequently the laws concern the existing
complex pullback, rather than a replacement defined to satisfy these laws.

`compositeSectionsComplexPullback R f g` constructs the successive section
map as a natural transformation

```text
C⁺(Γ_X) ⟶ (C⁺(L_f) ⋙ C⁺(L_g)) ⋙ C⁺(Γ_V),
```

using `s⁺_f`, the left whiskering of `s⁺_g`, and the functor associator.
`compositeSectionsComplexPullback_eq` identifies its composite with
`inverseImageComplexComp.hom` whiskered by `C⁺(Γ_V)` with `s⁺_(g≫f)`.
This is an equality of natural transformations in the bounded-below complex,
obtained from the component composition law.

## Provenance and remaining obligations

This is an internal consequence of the actual geometric inverse-image and
section constructions and the ordinary coherence in
`EtaleSectionPullbackCoherence`. Its original categorical ingredients are the
pinned Mathlib implementations in `Algebra/Homology/Additive.lean`:
`NatIso.mapHomologicalComplex`, `Functor.mapHomologicalComplexIdIso` and
`Functor.mapHomologicalComplexCompIso`; the bounded-below lift is the one in
`Algebra/Homology/CochainComplexPlus.lean`. The full-subcategory inclusion and
`Functor.preimageIso` provide only the lift of the already constructed maps.
The arguments above describe the implemented Lean proofs.

These are laws on actual bounded-below complexes. Their transport to the
existing derived and higher-cohomology maps, full geometric associativity
at those levels, agreement with the older etale-restriction model,
coefficient-ring coherence, compact supports, smooth actions and the Harris
specialization remain separate obligations. No inverse-image preservation
of injectives is assumed or claimed.
