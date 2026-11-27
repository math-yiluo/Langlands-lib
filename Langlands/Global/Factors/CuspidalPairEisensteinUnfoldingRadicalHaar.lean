import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenMeasure

/-! # The normalized Haar measure of the radical in matrix coordinates

In the additive matrix coordinates `Y ↦ u'(Y)` of the radical `U'(𝔸)`, the normalized Haar
measure `haarN` of the radical is a positive multiple of the Haar measure `openCellHaar` of the
matrix space `M_((t+1) × (r+1))(𝔸)`, by uniqueness of Haar measure. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Set
open scoped NNReal ENNReal

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal LeftCosetSpace

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

local instance radicalHaarAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F

local instance radicalHaarAdelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

local instance radicalHaarAdelesT2 : T2Space (Adeles F) :=
  GeneralLinearBlockSemidirect.adeleRing_t2Space F

local instance radicalMatrixMeasurableSpace :
    MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  borel _

local instance radicalMatrixBorelSpace :
    BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  ⟨rfl⟩

local instance radicalMatrixLocallyCompact :
    LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))

local instance radicalMatrixSecondCountable :
    SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (r + 1) → Adeles F))

/-- The additive matrix coordinates of the radical. -/
def radicalCoord : Radical F r t ≃ₜ Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) where
  toEquiv := Multiplicative.toAdd
  continuous_toFun := continuous_toAdd
  continuous_invFun := continuous_ofAdd

theorem radicalCoord_apply (n : Radical F r t) : radicalCoord F r t n = n.toAdd := rfl

instance openCellHaar_isAddHaarMeasure : (openCellHaar F r t).IsAddHaarMeasure := by
  unfold openCellHaar
  infer_instance

theorem haarN_fundamentalDomain :
    haarN F r t (fundamentalDomain ((Γ₀ F (r + t + 2)).comap (radicalHom F r t))
      (isDiscrete_radicalLattice F r t)) = 1 := by
  have := isFiniteMeasure_radicalQuotient F r t
  rw [haarN, Semidirect.latticeNormalizedHaar, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (haar_fundamentalDomain_ne_zero _ _)
      (haar_fundamentalDomain_ne_top _ _)]

/-- **Comparison of the radical Haar measures.** -/
theorem exists_map_radicalCoord_haarN :
    ∃ κ : ℝ≥0, 0 < κ ∧ (haarN F r t).map (radicalCoord F r t) = κ • openCellHaar F r t := by
  have hmeas : Measurable (radicalCoord F r t) := (radicalCoord F r t).continuous.measurable
  have hleft : ((haarN F r t).map (radicalCoord F r t)).IsAddLeftInvariant := by
    refine ⟨fun a => ?_⟩
    rw [Measure.map_map (measurable_const_add a) hmeas]
    have h : (fun x => a + x) ∘ radicalCoord F r t =
        radicalCoord F r t ∘ fun n => Multiplicative.ofAdd a * n := rfl
    have hN : (haarN F r t).IsMulLeftInvariant := by
      unfold haarN Semidirect.latticeNormalizedHaar
      infer_instance
    rw [h, ← Measure.map_map hmeas (measurable_const_mul _), MeasureTheory.map_mul_left_eq_self]
  have hfin : IsFiniteMeasureOnCompacts ((haarN F r t).map (radicalCoord F r t)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmeas hK.measurableSet]
    have hK' := (radicalCoord F r t).isCompact_preimage.mpr hK
    rw [haarN, Semidirect.latticeNormalizedHaar, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr
      (pos_iff_ne_zero.mpr (haar_fundamentalDomain_ne_zero _ _))) hK'.measure_lt_top
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarN F r t).map (radicalCoord F r t))
    (openCellHaar F r t)
  refine ⟨_, pos_iff_ne_zero.mpr fun h0 => ?_, heq⟩
  rw [h0, zero_smul, Measure.map_eq_zero_iff hmeas.aemeasurable] at heq
  have h1 := haarN_fundamentalDomain F r t
  rw [heq, Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- Integrals over the radical against `haarN`, in matrix coordinates. -/
theorem integral_haarN_eq {κ : ℝ≥0}
    (hκ : (haarN F r t).map (radicalCoord F r t) = κ • openCellHaar F r t)
    (G : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) → ℂ) :
    ∫ n, G n.toAdd ∂haarN F r t = ((κ : ℝ) : ℂ) * ∫ Y, G Y ∂openCellHaar F r t := by
  have h := (radicalCoord F r t).measurableEmbedding.integral_map (μ := haarN F r t) G
  rw [hκ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h
  exact h.symm

end Langlands.Global.CuspidalPairEisenstein.Unfolding
