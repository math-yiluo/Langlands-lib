# Products of open charts over a common base

Module `Langlands.AlgebraicGeometry.ProductOpenCharts`.

Let `p₁ : X₁ ⟶ T` and `p₂ : X₂ ⟶ T` be morphisms of schemes and `U₁ ⊆ X₁`, `U₂ ⊆ X₂` opens.

- `pOpen U₁ U₂` is the open `pr₁⁻¹ U₁ ⊓ pr₂⁻¹ U₂` of the fibre product `X₁ ×_T X₂`
  (`prodOpen` of `FieldTwoAxisH1Injectivity.ProductCover`).
- `incl U₁ U₂ : U₁ ×_T U₂ ⟶ X₁ ×_T X₂` is the induced open immersion, with `incl_fst`,
  `incl_snd`, and `range_incl` identifying its range with `pOpen U₁ U₂`.
- `prodIso U₁ U₂ : pOpen U₁ U₂ ≅ U₁ ×_T U₂` is the resulting isomorphism, and `prodIso_hom_fst`,
  `prodIso_hom_snd` identify its components with the restricted projections.
- For morphisms `κ₁ : U₁ ⟶ Z₁`, `κ₂ : U₂ ⟶ Z₂` over `T` (to `z₁ : Z₁ ⟶ T`, `z₂ : Z₂ ⟶ T`),
  `prodChart κ₁ κ₂ h₁ h₂ : pOpen U₁ U₂ ⟶ Z₁ ×_T Z₂` is their product; it is an open immersion when
  `κ₁` and `κ₂` are (`IsOpenImmersion` instance), and `prodChart_fst`, `prodChart_snd` compute its
  components.

These are elementary facts on fibre products of open immersions; the proofs use
`Scheme.Pullback.range_map` and `IsOpenImmersion.isoOfRangeEq` from Mathlib.
