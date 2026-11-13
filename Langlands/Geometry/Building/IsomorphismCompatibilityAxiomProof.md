# Proof of Axiom 4.1.17 for all supplied valuation data

`isomorphismCompatibilityAxiom : IsomorphismCompatibilityAxiomStatement.{u}`
proves the Library statement `IsomorphismCompatibilityAxiomStatement`. That
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
`algebraBaseMap F₁ F₂` is definitionally `specMapOfRingEquiv σ`, and the
statement's base change is the base change along this algebra. The proof
applies `ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension`
(module `IsomorphismCompatibilityFieldExtension`) and discharges its four
hypotheses:

- `horder`: `localFieldOrder_ringEquiv σ hσ`
  (module `LocalFieldOrderRingEquiv`). A valued-field isomorphism preserves
  the normalized order.
- `hθ`: `rationalExtend_bijective_of_bijective F₁ F₂ G₁ σ.bijective`
  (module `RingEquivBaseChange`). `G₁(F₁) → G₁(F₂)` is bijective because the
  algebra map is.
- `hN`: `GroupScheme.mem_normalizerPoints_rationalExtend_iff`
  (module `NormalizerPointsRingEquiv`). Extension of rational points reflects
  the normalizer of the base-changed torus `B₁.i` (a monomorphism by
  `mono_of_isMaximalSplitTorus`).
- `hmax`: `B₁.isMaximalSplitTorus.baseChange_fieldIso σ`
  (module `MaximalSplitTorusFieldIso`). Base change along a field
  isomorphism preserves maximal split tori.

The result is an equivariant isomorphism along
`(rationalPoints.map f_G.hom).comp (rationalExtend F₁ F₂ G₁)`.
`coveringPointsMap_eq_rationalExtend σ f_G.hom` (module
`CoveringPointsRingEquiv`) rewrites the statement's `coveringPointsMap σ f_G.hom`
into this form, which closes the goal.

No hypothesis beyond the statement's is used. In particular there is no
common-apartment, AS 5 or availability assumption. `lean_check` reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Axiom 4.1.17, printed p.162 (PDF p.193), read with the authors' corrections of
1 November 2024. Registered source IDs:
`kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The Lean route is internal: a chain of chart
isomorphisms through the field restriction of the transported apartment of
`B₂`, as described in `IsomorphismCompatibilityFieldExtension.md`.
