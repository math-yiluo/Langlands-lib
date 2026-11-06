import Langlands.LocalFactor.Abelian.Definitions
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! Fixed-Haar additive-character scaling of the actual abelian expression. -/

noncomputable section

open MeasureTheory
open scoped WithZero NNReal

namespace Langlands.HarmonicAnalysis.Quasicharacter

universe u
variable {F : Type u} [Field F] [TopologicalSpace F]

theorem extendZero_mul_unit (χ : Quasicharacter F) (a : Fˣ) (x : F) :
    extendZero χ ((a : F) * x) = (χ a : ℂ) * extendZero χ x := by
  by_cases hx : x = 0
  · simp [hx]
  · have he : Units.mk0 ((a : F) * x) (mul_ne_zero a.ne_zero hx) =
        a * Units.mk0 x hx := by
      ext
      rfl
    simp only [extendZero, dite_eq_right hx, dite_eq_right (mul_ne_zero a.ne_zero hx), he,
      map_mul, Units.val_mul]

theorem epsilonIntegrand_scale [IsTopologicalRing F] (χ : Quasicharacter F)
    (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (x : F) :
    epsilonIntegrand χ (ψ.scale a) x =
      (χ a : ℂ) * epsilonIntegrand χ ψ ((a : F) * x) := by
  simp only [epsilonIntegrand, UnitaryAdditiveCharacter.complex_apply,
    UnitaryAdditiveCharacter.scale_apply, extendZero_mul_unit, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ (χ a).ne_zero, one_mul]

end Langlands.HarmonicAnalysis.Quasicharacter

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- The multiplicative rank-one correction for scaling the additive character
while retaining the Haar measure. -/
def abelianScalingFactor (χ : MultiplicativeCharacter) : F.Carrierˣ →* ℂˣ where
  toFun a := χ a *
    (Units.mk0 (T.normalizedAbs (a : F.Carrier) : ℂ)
      (by exact_mod_cast (ne_of_gt (T.normalizedAbs_pos a.ne_zero))))⁻¹
  map_one' := by
    apply Units.ext
    simp [T.normalizedAbs_one]
  map_mul' a b := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
      T.normalizedAbs_mul, Complex.ofReal_mul, mul_inv]
    ac_rfl

@[simp]
theorem abelianScalingFactor_coe (χ : MultiplicativeCharacter) (a : F.Carrierˣ) :
    (T.abelianScalingFactor χ a : ℂ) =
      (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ := rfl

theorem additiveConductor_scale (ψ : AdditiveCharacter) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.additiveConductor (ψ.scale a) = T.additiveConductor ψ + T.ord (a : F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have htriv (n : ℤ) :
      T.AdditiveTrivialAt (ψ.scale a) n ↔
        T.AdditiveTrivialAt ψ (n - T.ord (a : F.Carrier)) := by
    unfold AdditiveTrivialAt
    rw [← T.forall_integers_uniformizer_mul_iff (ψ.scale a).toAddChar,
      ← T.forall_integers_uniformizer_mul_iff ψ.toAddChar]
    exact T.triviality_mulShift_iff ψ.toAddChar a n
  apply le_antisymm
  · have h := (T.additiveConductor_spec ψ).2 _
      ((htriv _).mp (T.additiveConductor_spec (ψ.scale a)).1)
    omega
  · apply (T.additiveConductor_spec (ψ.scale a)).2
    apply (htriv _).mpr
    simpa only [add_sub_cancel_right] using (T.additiveConductor_spec ψ).1

private theorem scaling_discreteValuation (a : F.Carrierˣ) :
    T.discreteValuation (a : F.Carrier) = WithZero.exp (-T.ord (a : F.Carrier)) := by
  simp only [ord, neg_neg]
  exact (WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr a.ne_zero)).symm

theorem mul_mem_valuationShell_iff (a : F.Carrierˣ) (k : ℤ) (x : F.Carrier) :
    (a : F.Carrier) * x ∈ T.valuationShell k ↔
      x ∈ T.valuationShell (k + T.ord (a : F.Carrier)) := by
  change T.discreteValuation ((a : F.Carrier) * x) = WithZero.exp k ↔
    T.discreteValuation x = WithZero.exp (k + T.ord (a : F.Carrier))
  rw [map_mul, T.scaling_discreteValuation a, mul_comm (WithZero.exp _) _,
    ← eq_div_iff WithZero.exp_ne_zero,
    ← WithZero.exp_sub]
  simp only [sub_neg_eq_add]

theorem epsilonShell_scale_preimage (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (fun x => (a : F.Carrier) * x) ⁻¹' T.epsilonShell χ ψ =
      T.epsilonShell χ (ψ.scale a) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  ext x
  simp only [Set.mem_preimage, epsilonShell, T.mul_mem_valuationShell_iff,
    T.additiveConductor_scale]
  rw [add_right_comm]

theorem abelianEpsilonExpression_scale_unramified (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ)
    (hχ : T.IsUnramifiedQuasicharacter χ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianEpsilonExpression χ (ψ.scale a) μ =
      (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ *
        T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let c := T.abelianScale (T.additiveConductor ψ)
  have hc : T.discreteValuation ((a * c : F.Carrierˣ) : F.Carrier) =
      WithZero.exp (-T.additiveConductor (ψ.scale a)) := by
    rw [Units.val_mul, map_mul, T.scaling_discreteValuation a,
      T.abelianScale_value, ← WithZero.exp_add, T.additiveConductor_scale]
    congr 1
    omega
  rw [T.abelianEpsilonExpression_unramified_scale χ (ψ.scale a) μ hχ (a * c) hc,
    T.abelianEpsilonExpression_unramified χ ψ μ hχ]
  change (χ (a * c) : ℂ) / (T.normalizedAbs ((a * c : F.Carrierˣ) : F.Carrier) : ℂ) *
    (T.integerVolume μ : ℂ) =
      (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ *
        ((χ c : ℂ) / (T.normalizedAbs (c : F.Carrier) : ℂ) *
          (T.integerVolume μ : ℂ))
  simp only [map_mul, Units.val_mul, T.normalizedAbs_mul, Complex.ofReal_mul,
    div_eq_mul_inv, mul_inv]
  ring

theorem abelianGaussIntegral_scale (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianGaussIntegral χ (ψ.scale a) μ =
      (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ *
        T.abelianGaussIntegral χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hmap := HarmonicAnalysis.padicScalarHaarScaling F T μ.measure a
  have hsub := (Homeomorph.mulLeft₀ (a : F.Carrier) a.ne_zero).measurableEmbedding.setIntegral_map
    (μ := μ.measure)
    (fun x => (χ a : ℂ) * HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ x)
    (T.epsilonShell χ ψ)
  change (∫ x in T.epsilonShell χ (ψ.scale a),
    HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ (ψ.scale a) x ∂μ.measure) = _
  calc
    _ = ∫ x in (fun x => (a : F.Carrier) * x) ⁻¹' T.epsilonShell χ ψ,
        (χ a : ℂ) * HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ
          ((a : F.Carrier) * x) ∂μ.measure := by
      rw [T.epsilonShell_scale_preimage]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (HarmonicAnalysis.Quasicharacter.epsilonIntegrand_scale χ ψ a)
    _ = ∫ x in T.epsilonShell χ ψ,
        (χ a : ℂ) * HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ x
          ∂μ.measure.map (fun x => (a : F.Carrier) * x) := hsub.symm
    _ = ((T.normalizedAbsUnits a : ℝ≥0)⁻¹) •
        ∫ x in T.epsilonShell χ ψ,
          (χ a : ℂ) * HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ x
            ∂μ.measure := by
      rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
    _ = (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ *
        T.abelianGaussIntegral χ ψ μ := by
      rw [integral_const_mul]
      simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
        T.normalizedAbsUnits_coe, Complex.ofReal_inv, abelianGaussIntegral]
      ring

theorem abelianEpsilonExpression_scale (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianEpsilonExpression χ (ψ.scale a) μ =
      (χ a : ℂ) * (T.normalizedAbs (a : F.Carrier) : ℂ)⁻¹ *
        T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hχ : T.IsUnramifiedQuasicharacter χ
  · exact T.abelianEpsilonExpression_scale_unramified χ ψ μ a hχ
  · rw [T.abelianEpsilonExpression_ramified χ (ψ.scale a) μ hχ,
      T.abelianEpsilonExpression_ramified χ ψ μ hχ]
    exact T.abelianGaussIntegral_scale χ ψ μ a

theorem abelianEpsilonExpression_scale_factor (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianEpsilonExpression χ (ψ.scale a) μ =
      (T.abelianScalingFactor χ a : ℂ) * T.abelianEpsilonExpression χ ψ μ :=
  T.abelianEpsilonExpression_scale χ ψ μ a

end Langlands.PadicField.TopologicalData
