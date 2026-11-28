import Langlands.Global.AdelicRelativeCorootHaar
import Langlands.Global.AdelicRelativeParabolicDensity
import Langlands.Global.AdelicIntertwiningLeviRestriction

/-! # Cancellation of the split Iwasawa density in the normalized shell integral -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "A" => fam.A J
local notation "p" => fam.p J
local notation "l" => fam.l J
local notation "a" => fam.a J
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "C" => fam.relativeSimpleRoots J
local notation "density" => relativePositiveDensity p l a

/-- The relative split coordinate, viewed as an actual point of the parabolic. -/
def relativeParabolicSplitPoint (b : B) : AdelicGroupPoints F P :=
  map F M P l (positivePointMap F M A a b.val)

/-- The relative split lift is in the parabolic positive split component. -/
theorem relativeParabolicSplitPoint_mem (b : B) :
    fam.relativeParabolicSplitPoint J b ∈ fam.positiveSplitComponent J := by
  refine ⟨b.val.val, b.val.property, ?_⟩
  change map F (A).toGrp P (a ≫ l) b.val.val = fam.relativeParabolicSplitPoint J b
  rw [map_comp_apply_of_hom]
  rfl

private theorem halfModulus_sq (x : AdelicGroupPoints F P) :
    fam.halfModulus J x ^ 2 = parameterPower F P (modulusParameter F P) x := by
  rw [pow_two, halfModulus, ← StandardParabolicFamily.parameterPower_add]
  congr 2
  simp only [halfModulusParameter, modulusParameter, ← TensorProduct.add_tmul]
  norm_num

/-- The real value of the split density is exactly the reciprocal of the squared
half-modulus used to normalize the pairing. -/
theorem relativePositiveDensity_toReal (b : B) :
    ((density b).toReal : ℂ) = (fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2)⁻¹ := by
  have hd : 0 ≤ inverseModulus l (positivePointMap F M A a b.val) := norm_nonneg _
  rw [relativePositiveDensity, ENNReal.toReal_ofReal hd, ofReal_inverseModulus,
    parameterPower_neg, fam.halfModulus_sq J]
  rfl

private theorem splitDensity_measurable : Measurable (density : B → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((continuous_inverseModulus l).measurable.comp
    ((positivePointMap F M A a).continuous.measurable.comp measurable_subtype_coe))

private theorem splitCompensation (b : B) :
    ((density b).toReal : ℂ) * (fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2) = 1 := by
  rw [fam.relativePositiveDensity_toReal J, fam.halfModulus_sq J,
    inv_mul_cancel₀ (parameterPower_ne_zero _ _)]

/-- In the relative split integral the squared half-modulus cancels the density. -/
theorem integral_relativePositiveDensity_cancel (da : Measure B) [SFinite da]
    (S : Set B) (f : B → ℂ) :
    (∫ b in S, fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2 * f b
      ∂(da.withDensity density)) = ∫ b in S, f b ∂da := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul' S (fam.splitDensity_measurable J)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    change (density b).toReal •
      (fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2 * f b) = f b
    rw [Complex.real_smul, ← mul_assoc, fam.splitCompensation J, one_mul]

/-- The same cancellation holds for the norm of the complex integrand. -/
theorem integral_norm_relativePositiveDensity_cancel (da : Measure B) [SFinite da]
    (S : Set B) (f : B → ℂ) :
    (∫ b in S, ‖fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2 * f b‖
      ∂(da.withDensity density)) = ∫ b in S, ‖f b‖ ∂da := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul' S (fam.splitDensity_measurable J)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    have hc := congrArg Norm.norm (fam.splitCompensation J b)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, norm_one] at hc
    change (density b).toReal •
      ‖fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2 * f b‖ = ‖f b‖
    rw [smul_eq_mul, norm_mul, ← mul_assoc, hc, one_mul]

/-- In the relative coroot coordinates the normalized split integral is Lebesgue integration
with one positive scalar for each chosen Haar measure. -/
def RelativeSplitIntegralStatement : Prop :=
  ∃ e : B ≃ₜ* Multiplicative (C → ℝ),
    (∀ b : B,
      characterLog F P (fam.relativeParabolicSplitPoint J b) =
        ∑ α : C, (e b).toAdd α • fam.relativeCoroot J α) ∧
    ∀ da : Measure B, da.IsHaarMeasure → SigmaFinite da → ∃ c > (0 : ℝ≥0),
      ∀ (S : Set B) (f : (C → ℝ) → ℂ),
        (∫ b in S, fam.halfModulus J (fam.relativeParabolicSplitPoint J b) ^ 2 * f (e b).toAdd
          ∂(da.withDensity density)) = (c : ℂ) *
          ∫ u in (fun b => (e b).toAdd) '' S, f u

/-- Cancel the density and transport the restricted measure by the coroot logarithm. -/
theorem relativeSplitIntegral : fam.RelativeSplitIntegralStatement J := by
  obtain ⟨e, hlog, hHaar⟩ := fam.relativeCorootHaar J
  refine ⟨e, fun b => (hlog b).2, fun da hda hsf => ?_⟩
  let : SigmaFinite da := hsf
  obtain ⟨c, hc, hp⟩ := hHaar da hda
  refine ⟨c, hc, fun S f => ?_⟩
  let L : B ≃ₜ (C → ℝ) :=
    { toEquiv := e.toEquiv.trans Multiplicative.toAdd
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hL : MeasurePreserving L da (c • (volume : Measure (C → ℝ))) := hp
  have hr := hL.restrict_image_emb L.toMeasurableEquiv.measurableEmbedding S
  rw [fam.integral_relativePositiveDensity_cancel J da S (fun b => f (e b).toAdd)]
  calc
    _ = ∫ u in L '' S, f u ∂(c • (volume : Measure (C → ℝ))) :=
      hr.integral_comp L.toMeasurableEquiv.measurableEmbedding f
    _ = _ := by
      rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
      rfl

end Langlands.Global.StandardParabolicFamily
