# Proof of Axiom 4.1.17 for all supplied valuation data

`Langlands.Geometry.Building.isomorphismCompatibilityAxiom :
IsomorphismCompatibilityAxiomStatement.{u}` proves the Library statement
`Langlands.Geometry.Building.IsomorphismCompatibilityAxiomStatement` (module
`Langlands.Geometry.Building.IsomorphismCompatibilityAxiomStatement`). That
statement is Kaletha–Prasad Axiom 4.1.17 (compatibility with isomorphisms) for
arbitrary supplied valuation data on both sides. Fix nonarchimedean local
fields `F₁`, `F₂`, an isomorphism of valued fields `σ : F₁ ≃+* F₂`
(`IsValuativeRingEquiv σ`), affine group schemes `G₁`, `G₂`, an isomorphism
`f_G : G₁ ×_{F₁,σ} F₂ ≅ G₂`, and data `B₁`, `B₂`. Then some bijection `Φ` of the
reduced buildings is an `IsEquivariantBuildingIso` along
`coveringPointsMap σ f_G.hom`.

## Proof

Make `F₂` an `F₁`-algebra through `σ`
(`let : Algebra F₁ F₂ := σ.toRingHom.toAlgebra`). Then
`algebraBaseMap F₁ F₂ = Spec.map (CommRingCat.ofHom (algebraMap F₁ F₂))` is
definitionally `specMapOfRingEquiv σ = Spec.map (CommRingCat.ofHom σ.toRingHom)`,
so the statement's base change along `specMapOfRingEquiv σ` is the base change
along this algebra.

The proof applies
`Langlands.Geometry.Building.ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension`
(module `Langlands.Geometry.Building.IsomorphismCompatibilityFieldExtension`).
For `f_G` and the given `B₁`, `B₂`, this theorem gives an equivariant
isomorphism of the reduced buildings along
`(rationalPoints.map f_G.hom).comp (rationalExtend F₁ F₂ G₁)`. It needs four
hypotheses, discharged as follows:

- `horder` (the field map preserves the normalized order `localFieldOrder`):
  `Langlands.Geometry.Building.localFieldOrder_ringEquiv σ hσ`
  (module `Langlands.Geometry.Building.LocalFieldOrderRingEquiv`). A
  valued-field isomorphism preserves the normalized order.
- `hθ` (`G₁(F₁) → G₁(F₂)` is bijective):
  `Langlands.GroupScheme.GaloisPointComparison.rationalExtend_bijective_of_bijective F₁ F₂ G₁ σ.bijective`
  (module `Langlands.GroupScheme.Rational.RingEquivBaseChange`). Extension of
  rational points is bijective because the algebra map is.
- `hN` (extension of rational points reflects the normalizer of the
  base-changed torus):
  `Langlands.GroupScheme.mem_normalizerPoints_rationalExtend_iff B₁.i`
  (module `Langlands.Geometry.Building.NormalizerPointsRingEquiv`). This
  needs `B₁.i` to be a monomorphism on underlying schemes, supplied by
  `Langlands.Geometry.Building.mono_of_isMaximalSplitTorus B₁.isMaximalSplitTorus`
  (module `Langlands.Geometry.Building.ValuationBuildingData`).
- `hmax` (the base change of the torus of `B₁` is a maximal split torus):
  `B₁.isMaximalSplitTorus.baseChange_fieldIso σ`, that is,
  `Langlands.GroupScheme.IsMaximalSplitTorus.baseChange_fieldIso`
  (module `Langlands.GroupScheme.Rational.MaximalSplitTorusFieldIso`). Base
  change along a field isomorphism preserves maximal split tori.

Finally
`Langlands.Geometry.Building.coveringPointsMap_eq_rationalExtend σ f_G.hom`
(module `Langlands.Geometry.Building.CoveringPointsRingEquiv`) rewrites the
statement's `coveringPointsMap σ f_G.hom` into
`(rationalPoints.map f_G.hom).comp (rationalExtend F₁ F₂ G₁)`, and the
isomorphism obtained above closes the goal.

No hypothesis beyond the statement's is used. In particular there is no
common-apartment, V 7, AS 5, building-axiom or availability assumption.
`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` reports
kind `theorem`, no errors or warnings, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Axiom 4.1.17, printed p.162 (PDF p.193), read with the authors' corrections of
1 November 2024. Registered source IDs:
`kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. KP 4.1.28 (printed p.166 / PDF p.197)
states that the axiom is proved in Proposition 7.9.5 (printed p.276 / PDF
p.307), whose proof matches facets through parahoric subgroups. The Lean route
is internal and does not follow that proof. It goes through a chain of chart
isomorphisms via the field restriction of the transported apartment of `B₂`,
as described in `IsomorphismCompatibilityFieldExtension.md`.
