import Langlands.Global.AdelicInducedInnerProduct
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Concatenation of spectral coordinates and product coefficients -/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace Langlands.Global.AdelicGroupPoints

instance spectralMeasure_sFinite (n : ℕ) : SFinite (spectralMeasure n) := by
  unfold spectralMeasure
  infer_instance

/-- The linear concatenation of `ℝᵐ × ℝⁿ` onto `ℝᵐ⁺ⁿ`, with the relative coordinate block
first and the ambient coordinate block second. -/
def spectralCoordinateProduct (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin (m + n) → ℝ) :=
  (LinearEquiv.sumPiEquivProdPi ℝ (Fin m) (Fin n) fun _ => ℝ).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm)

/-- The underlying coordinate concatenation preserves ordinary product Lebesgue measure. -/
theorem measurePreserving_spectralCoordinateProduct_volume (m n : ℕ) :
    MeasurePreserving (spectralCoordinateProduct m n) volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => ℝ)
  have h₂ := volume_preserving_arrowCongr' (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  exact h₂.comp h₁

/-- The same concatenation transports the product of the two existing spectral measures to
`spectralMeasure (m+n)`, including the exact `(2π)^(-(m+n))` factor. -/
theorem measurePreserving_spectralCoordinateProduct (m n : ℕ) :
    MeasurePreserving (spectralCoordinateProduct m n) ((spectralMeasure m).prod (spectralMeasure n))
      (spectralMeasure (m + n)) := by
  have h := measurePreserving_spectralCoordinateProduct_volume m n
  refine ⟨h.measurable, ?_⟩
  unfold spectralMeasure
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ h.measurable.aemeasurable]
  change _ • Measure.map (spectralCoordinateProduct m n) volume = _
  rw [h.map_eq, ← pow_add]

/-- Product of the two coefficient functions in the concatenated spectral coordinates. -/
def spectralProductCoefficient {m n : ℕ} (c : (Fin m → ℝ) → ℂ) (d : (Fin n → ℝ) → ℂ) :
    (Fin (m + n) → ℝ) → ℂ :=
  fun z => c ((spectralCoordinateProduct m n).symm z).1 * d ((spectralCoordinateProduct m n).symm z).2

@[simp] theorem spectralProductCoefficient_apply_product {m n : ℕ}
    (c : (Fin m → ℝ) → ℂ) (d : (Fin n → ℝ) → ℂ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    spectralProductCoefficient c d (spectralCoordinateProduct m n x) = c x.1 * d x.2 := by
  simp [spectralProductCoefficient]

/-- Concatenation preserves the smoothness of product coefficients. -/
theorem ContDiff.spectralProductCoefficient {m n : ℕ} {k : ℕ∞}
    {c : (Fin m → ℝ) → ℂ} {d : (Fin n → ℝ) → ℂ}
    (hc : ContDiff ℝ k c) (hd : ContDiff ℝ k d) : ContDiff ℝ k (spectralProductCoefficient c d) := by
  let E := (spectralCoordinateProduct m n).symm.toContinuousLinearEquiv
  have hE : ContDiff ℝ k E := E.toContinuousLinearMap.contDiff
  exact (hc.comp (contDiff_fst.comp hE)).mul (hd.comp (contDiff_snd.comp hE))

/-- The new coefficient has compact support if both factors do. -/
theorem HasCompactSupport.spectralProductCoefficient {m n : ℕ}
    {c : (Fin m → ℝ) → ℂ} {d : (Fin n → ℝ) → ℂ}
    (hc : HasCompactSupport c) (hd : HasCompactSupport d) : HasCompactSupport (spectralProductCoefficient c d) := by
  let E := spectralCoordinateProduct m n
  have hK : IsCompact (E '' (tsupport c ×ˢ tsupport d)) :=
    (hc.prod hd).image E.toContinuousLinearEquiv.continuous
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  intro z hz
  change c (E.symm z).1 * d (E.symm z).2 ≠ 0 at hz
  exact ⟨E.symm z, ⟨subset_closure (left_ne_zero_of_mul hz),
    subset_closure (right_ne_zero_of_mul hz)⟩, E.apply_symm_apply z⟩

/-- Separation of the product integral in concatenated spectral coordinates. The statement
uses Mathlib's total Bochner integral convention. -/
theorem integral_spectralProductCoefficient {m n : ℕ}
    (c : (Fin m → ℝ) → ℂ) (d : (Fin n → ℝ) → ℂ) :
    ∫ z, spectralProductCoefficient c d z ∂(spectralMeasure (m + n)) =
      (∫ x, c x ∂(spectralMeasure m)) * (∫ y, d y ∂(spectralMeasure n)) := by
  have h := measurePreserving_spectralCoordinateProduct m n
  let E := (spectralCoordinateProduct m n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  rw [← h.integral_comp E.measurableEmbedding]
  simpa only [spectralProductCoefficient_apply_product] using (integral_prod_mul c d)

end Langlands.Global.AdelicGroupPoints
