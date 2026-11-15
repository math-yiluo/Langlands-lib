import Langlands.Global.RankinSelberg.UnequalAnalyticDecay
import Langlands.Global.RankinSelberg.UnequalAnalyticProjection
import Langlands.Automorphic.OperatorDeterminantSliceMeasure

/-! # Weighted integrability of cusp forms on `GL_n(F) \ GL_n(𝔸)`

For a cuspidal vector `f` of an operator realization of `GL_n`, the function
`q ↦ |f(q)| exp (-B |log |det q||)` has finite integral over `GL_n(F) \ GL_n(𝔸)` for all large
`B`. The proof transfers the weighted cover of `UnequalAnalyticDecay` (a measurable set meeting
every rational orbit, on which the weighted integral is finite) to the quotient, using the
Library covering bound `LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le`. A
general lemma then turns such a bound, together with a pointwise estimate, into Bochner
integrability. -/

noncomputable section
universe u
set_option autoImplicit false

open NumberField MeasureTheory Langlands Langlands.Global Langlands.Automorphic
  Langlands.Automorphic.ContinuousRationalFunctions
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

local instance integrabilitySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance integrabilitySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Integrability from a dominating function of finite integral.** -/
theorem integrable_of_enorm_le {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f ν) {w : X → ℝ≥0∞} (hw : ∫⁻ x, w x ∂ν < ⊤) (C : ℝ)
    (hle : ∀ x, ‖f x‖ₑ ≤ ENNReal.ofReal C * w x) : Integrable f ν := by
  refine ⟨hf, ?_⟩
  calc ∫⁻ x, ‖f x‖ₑ ∂ν ≤ ∫⁻ x, ENNReal.ofReal C * w x ∂ν := lintegral_mono hle
    _ = ENNReal.ofReal C * ∫⁻ x, w x ∂ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- **Transfer of a weighted cover to the quotient.** Let `φ₀` be continuous and left invariant
under `GL_n(F)`, and let `t` be a measurable set meeting every rational orbit on which
`|φ₀| exp (-B |log |det||)` has finite integral for the Haar measure. Then the same weighted
function has finite integral over `GL_n(F) \ GL_n(𝔸)`. -/
theorem lintegral_quotient_lt_top_of_cover [MeasurableSpace (AdelicGL F n)]
    [BorelSpace (AdelicGL F n)] (φ₀ : AdelicGL F n → ℂ) (hφc : Continuous φ₀)
    (hφr : ∀ (c : RationalGL F n) (g : AdelicGL F n), φ₀ (AdelicGL.rational F n c * g) = φ₀ g)
    (B : ℝ) (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcov : ∀ g : AdelicGL F n, ∃ c : RationalGL F n, AdelicGL.rational F n c * g ∈ t)
    (hint : ∫⁻ x in t, ‖φ₀ x‖ₑ * ENNReal.ofReal (Real.exp (-(B * |Real.log (absDet F n x)|)))
      ∂Measure.map (e n) Measure.haar < ⊤) :
    ∫⁻ q, ‖φ₀ (e n (Quotient.out q))‖ₑ *
        ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F n (Quotient.out q))|)))
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) < ⊤ := by
  let Γ := AdelicGroupPoints.rationalSubgroup F (Scheme F n)
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n)
  let w : Points F n → ℝ≥0∞ := fun x =>
    ‖φ₀ (e n x)‖ₑ * ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F n x)|)))
  have hwm : Measurable w := by
    refine ((hφc.comp (e n).continuous).measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))
    exact (measurable_const.mul ((continuous_detNorm F n).measurable.log.abs)).neg
  have hw : ∀ (c : Γ) (x : Points F n), w ((c : Points F n) * x) = w x := by
    rintro ⟨_, c, rfl⟩ x
    have h1 : φ₀ (e n (AdelicGroupPoints.rational F (Scheme F n) c * x)) = φ₀ (e n x) := by
      rw [map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational]
      exact hφr _ _
    show w (AdelicGroupPoints.rational F (Scheme F n) c * x) = w x
    simp only [w, detNorm_rational_mul, h1]
  have hfun : (fun q : AdelicGroupPoints.RationalQuotient F (Scheme F n) =>
      ‖φ₀ (e n (Quotient.out q))‖ₑ *
        ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F n (Quotient.out q))|)))) =
      LeftCosetSpace.lift Γ w hw := funext fun q => (lift_eq_out Γ w hw q).symm
  have hliftm : Measurable (LeftCosetSpace.lift Γ w hw) := measurable_from_quotient.2 hwm
  have hcov' : ∀ x : Points F n, LeftCosetSpace.mk Γ x ∈ Set.univ →
      ∃ c : Γ, (c : Points F n) * x ∈ (e n) ⁻¹' t := by
    intro x _
    obtain ⟨c, hc⟩ := hcov (e n x)
    let c' := (GeneralLinearGroupPoints.rationalEquiv F n).symm c
    refine ⟨⟨AdelicGroupPoints.rational F (Scheme F n) c', ⟨c', rfl⟩⟩, ?_⟩
    change e n (AdelicGroupPoints.rational F (Scheme F n) c' * x) ∈ t
    simpa only [c', map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hc
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le Γ hΓ
    Measure.haar Set.univ MeasurableSet.univ ((e n) ⁻¹' t)
    (ht.preimage (e n).continuous.measurable) hcov' (LeftCosetSpace.lift Γ w hw) hliftm
  rw [Measure.restrict_univ] at hle
  rw [hfun]
  refine hle.trans_lt (lt_of_eq_of_lt ?_ hint)
  have hGm : Measurable fun y : AdelicGL F n =>
      ‖φ₀ y‖ₑ * ENNReal.ofReal (Real.exp (-(B * |Real.log (absDet F n y)|))) := by
    refine (hφc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))
    exact (measurable_const.mul ((continuous_absDet F n).measurable.log.abs)).neg
  have hem : Measurable fun x : Points F n => e n x := (e n).continuous.measurable
  rw [← lintegral_indicator ht _, lintegral_map (g := fun x => e n x) (hGm.indicator ht) hem,
    ← lintegral_indicator (ht.preimage hem) _]
  rfl

/-- **Weighted integrability of a cusp form on the quotient.** -/
theorem exists_lintegral_quotient_lt_top [CompactSpace (AdeleQuotient F)]
    (S : OperatorRealization F n) (hS : S.IsCuspidal) (f : S.Space) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      ∫⁻ q, ‖evaluate F n (S.toContinuous f) (e n (Quotient.out q))‖ₑ *
          ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F n (Quotient.out q))|)))
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) < ⊤ := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcov, hint⟩ := exists_weighted_cover S hS
  obtain ⟨B₀, hB₀⟩ := hint f
  refine ⟨B₀, fun B hB => ?_⟩
  have : (Measure.map (e n) (Measure.haar : Measure (Points F n))).IsHaarMeasure :=
    (e n).isHaarMeasure_map Measure.haar
  exact lintegral_quotient_lt_top_of_cover F _ (continuous_evaluate F n _)
    (evaluate_rational F n _) B t ht hcov (hB₀ B hB _)

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
