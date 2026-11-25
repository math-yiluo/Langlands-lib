# Integrability on lines and exhaustion by compact sets in `ℝⁿ`

Module `Langlands.Analysis.SeveralComplex.LineIntegrability` (namespace
`Langlands.Analysis.SeveralComplex`). Helper of
`Langlands.Analysis.SeveralComplex.RealHyperplaneDivision` (for Lapid
2011 Proposition 6). Provenance: internal; standard measure theory (Fubini
along a shear, monotone exhaustion), proved from Mathlib.

## Declarations

- `headTailEquiv n : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)`, Mathlib's
  `MeasurableEquiv.piFinSuccAbove` at `0`: `headTailEquiv_apply` says it is
  `x ↦ (x 0, Fin.tail x)`, `headTailEquiv_symm_apply` that the inverse is
  `(t, y) ↦ Fin.cons t y`, and `measurePreserving_headTailEquiv` that it
  preserves Lebesgue measure.
- `shear w : ℝ × (Fin n → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)`, `(t, y) ↦ (t, y + t • w)`,
  with inverse `(t, y) ↦ (t, y - t • w)` (`shear_apply`, `shear_symm_apply`);
  `measurePreserving_shear`: it preserves the product Lebesgue measure
  (`MeasurePreserving.skew_product` with translations in the fibres).
- `exists_ae_integrableOn_line`: let `v : Fin (n + 1) → ℝ` with `v 0 = 1`,
  `f` integrable on `ball 0 ρ`, and `0 < T` with `4 T (1 + ‖v‖) ≤ ρ`. Then for
  almost every `x` with `‖x‖ < min T (ρ / (2 (1 + ‖v‖)))` the function
  `t ↦ f (x + t • v)` is integrable on `(-T, T)`.
- `integrableOn_of_forall_isCompact_le`: let `U ⊆ ℝⁿ` be open and bounded,
  `Z` closed with `volume Z = 0`, `f ≥ 0` continuous on `U \ Z`, and
  `∫_A f ≤ C` for every compact `A ⊆ U` disjoint from `Z`. Then `f` is
  integrable on `U`.

## Proofs

`exists_ae_integrableOn_line`. Write `v = (1, w)`. The maps
`Φ = headTailEquiv⁻¹ ∘ shear w`, `Φ (s, y) = (s, y + s w)`, and its inverse
`Ψ x = (x 0, tail x - x 0 · w)` preserve measure, and
`Φ (x 0 + t, (Ψ x).2) = x + t v`. The function
`F = 1_{ball 0 ρ} · f` is integrable, hence so is `F ∘ Φ` on the product, and
by Fubini (`Integrable.prod_left_ae`) `s ↦ F (Φ (s, y))` is integrable for
`y` outside a null set `N`. Its preimage `Ψ⁻¹ (univ × N)` is null. For `x`
outside it, `t ↦ F (Φ ((Ψ x).1 + t, (Ψ x).2))` is integrable (translation,
`Integrable.comp_add_left`), and on `(-T, T)` it equals `f (x + t v)`
because `‖x + t v‖ < r + T ‖v‖ < ρ` for `‖x‖ < r = min T (ρ / (2 (1 + ‖v‖)))`.

`integrableOn_of_forall_isCompact_le`. The open set `U \ Z` is an increasing
union of closed sets `K j` (`IsOpen.exists_iUnion_isClosed`), compact since
`U` is bounded. On each, `f` is continuous, so
`∫⁻_{K j} f = ∫_{K j} f ≤ C`; by monotone convergence
(`setLIntegral_iUnion_of_directed`) `∫⁻_{U \ Z} f ≤ C < ∞`, and `f` is
a.e. strongly measurable on `U \ Z`. Finally `U \ Z` and `U` agree up to the
null set `U ∩ Z`.
