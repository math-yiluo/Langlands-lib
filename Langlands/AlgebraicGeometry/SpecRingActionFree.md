# Free finite group actions on affine schemes from ring actions

A group `Γ : Type u` acting on a commutative ring `B : Type u` by ring
automorphisms acts on `Spec B`. This module packages the action as a Library
`FiniteFreeSchemeAction Γ (Spec B)` (from
`Langlands.AlgebraicGeometry.FiniteFreeSchemeActionRelation`), under a pointwise
freeness hypothesis. It is an internal module for the chart construction of
`Langlands.GroupScheme.HomScheme.TorusChartConstruction`.

- `specIso e`: the automorphism `Spec.map e` of `Spec B` for a ring
  automorphism `e`, with inverse `Spec.map e⁻¹`.
- `finiteFreeSchemeAction σ hfree`, for `σ : Γ →* (B ≃+* B)`: the action
  `γ ↦ specIso (σ γ)`. The unit and composition laws follow from functoriality
  of `Spec.map`. The order is right because `Spec.map` is contravariant and
  `σ (g h) = σ g ∘ σ h`.
  The hypothesis `hfree` says: for every field `K : Type u` and ring map
  `φ : B → K`, `φ ∘ σ g = φ ∘ σ h` implies `g = h`. Freeness on
  nonempty test schemes `T`: choose a point `t`, compose with
  `T.fromSpecResidueField t`, and write the composite to `Spec B` as
  `Spec.map φ` (`Spec.preimage`). Faithfulness of `Spec`
  (`Spec.map_injective`) turns equality of the two translates into
  `φ ∘ σ g = φ ∘ σ h`.
