import Langlands.Global.RankinSelberg.RealGodementAdditiveJacquet
import Langlands.Representation.Whittaker.DualTransform
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Weyl inverse-transpose of the real open-cell Jacquet integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "w" => weylLong (t + 1) ℝ
local notation "iT" => inverseTranspose (t + 1) ℝ

private theorem reflectedUnipotent_twice (u : N) : reflectedUnipotent (reflectedUnipotent u) = u := by
  apply Subtype.ext
  simp only [reflectedUnipotent_val, map_mul, inverseTranspose_weylLong, inverseTranspose_involutive]
  calc
    _ = (w * w) * u.val * (w * w) := by simp only [mul_assoc]
    _ = _ := by rw [weylLong_mul_self, one_mul, mul_one]

private theorem reflectedUnipotent_mul (u v : N) :
    reflectedUnipotent (u * v) = reflectedUnipotent u * reflectedUnipotent v := by
  apply Subtype.ext
  simp only [reflectedUnipotent_val, Subgroup.coe_mul, map_mul]
  calc
    _ = w * (iT u.val * (w * w) * iT v.val) * w := by rw [weylLong_mul_self, mul_one]
    _ = _ := by simp only [mul_assoc]

private theorem continuous_reflectedUnipotent : Continuous (reflectedUnipotent (F := ℝ) (n := t)) :=
  (((continuous_const.mul ((continuous_inverseTranspose (t + 1) ℝ).comp continuous_subtype_val)).mul
    continuous_const).subtype_mk fun u => (reflectedUnipotent u).property)

private def reflectedUnipotentEquiv : N ≃ₜ* N where
  toFun := reflectedUnipotent
  invFun := reflectedUnipotent
  left_inv := reflectedUnipotent_twice
  right_inv := reflectedUnipotent_twice
  map_mul' := reflectedUnipotent_mul
  continuous_toFun := continuous_reflectedUnipotent
  continuous_invFun := continuous_reflectedUnipotent

private theorem measurePreserving_reflectedUnipotent (a : ℝˣ) :
    MeasurePreserving (reflectedUnipotent (F := ℝ) (n := t)) (upperStepHaar t a) (upperStepHaar t a) := by
  let coords := upperEntryCoordinates (t + 1) (K := ℝ)
  let : LocallyCompactSpace N := coords.isClosedEmbedding.locallyCompactSpace
  let : SigmaCompactSpace N := coords.isClosedEmbedding.sigmaCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace N := coords.isEmbedding.isInducing.pseudoMetrizableSpace
  let μ := upperStepHaar t a
  let : μ.IsHaarMeasure := upperStepHaar_isHaar t a
  let : μ.Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let e : N ≃ₜ* N := reflectedUnipotentEquiv
  have he : e.trans e = ContinuousMulEquiv.refl N := by
    ext1 u
    exact reflectedUnipotent_twice u
  have he2 : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, he, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar e = 1 := by
    apply NNReal.eq
    change (mulEquivHaarChar e : ℝ) = 1
    have h2 : (mulEquivHaarChar e : ℝ) * (mulEquivHaarChar e : ℝ) = 1 := by exact_mod_cast he2
    have hzero : ((mulEquivHaarChar e : ℝ) - 1) * ((mulEquivHaarChar e : ℝ) + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hzero with h | h
    · linarith
    · linarith [NNReal.coe_nonneg (mulEquivHaarChar e)]
  have hm := mulEquivHaarChar_smul_map μ e
  rw [h1, one_smul] at hm
  exact ⟨continuous_reflectedUnipotent.measurable, hm⟩

private theorem weylInverseTranspose_openCell (u : N) (g : G) :
    weylInverseTranspose (t + 1) ℝ (w * u.val * g) =
      w * (reflectedUnipotent u).val * weylInverseTranspose (t + 1) ℝ g := by
  have hW (x : G) : weylInverseTranspose (t + 1) ℝ (w * x) =
      w * weylInverseTranspose (t + 1) ℝ x := by
    simp only [weylInverseTranspose_apply, map_mul, inverseTranspose_weylLong]
  rw [mul_assoc w u.val g, hW, weylInverseTranspose_left_unipotent, ← mul_assoc]

private theorem standardCharacter_reflected_real (a : ℝˣ) (u : N) :
    (standardCharacter (realScaledCharacter a) t (reflectedUnipotent u) : ℂ) =
      (standardCharacter (realScaledCharacter (-a)) t u : ℂ) := by
  simp only [standardCharacter_apply, reflectedUnipotent_sum]
  let s := ∑ i : Fin t, u.val.val i.castSucc i.succ
  change realStandardCharacter.complex ((a : ℝ) * (-s)) =
    realStandardCharacter.complex (((-a : ℝˣ) : ℝ) * s)
  rw [Units.val_neg, mul_neg, neg_mul]

private theorem additiveJacquetIntegral_dual (a : ℝˣ) (f : G → ℂ) (g : G) :
    additiveJacquetIntegral (-a) (ArchimedeanLocal.dualFunction (t + 1) f) g =
      ArchimedeanLocal.dualFunction (t + 1) (additiveJacquetIntegral a f) g := by
  let e := (reflectedUnipotentEquiv (t := t)).toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (upperStepHaar t a) (upperStepHaar t a) :=
    measurePreserving_reflectedUnipotent a
  change (∫ u, additiveJacquetKernel (-a) (ArchimedeanLocal.dualFunction (t + 1) f) g u
      ∂upperStepHaar t (-a)) =
    ∫ u, additiveJacquetKernel a f (weylInverseTranspose (t + 1) ℝ g) u ∂upperStepHaar t a
  rw [upperStepHaar_neg, ← hp.integral_comp' (additiveJacquetKernel a f (weylInverseTranspose (t + 1) ℝ g))]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  change f (weylInverseTranspose (t + 1) ℝ (w * u.val * g)) *
      (standardCharacter (realScaledCharacter (-a)) t u : ℂ) =
    f (w * (reflectedUnipotent u).val * weylInverseTranspose (t + 1) ℝ g) *
      (standardCharacter (realScaledCharacter a) t (reflectedUnipotent u) : ℂ)
  rw [weylInverseTranspose_openCell, standardCharacter_reflected_real]

/-- Weyl inverse transpose of the open-cell Jacquet value is the integral of
the Weyl inverse-transpose function with the opposite additive parameter. -/
def RealGodementOpenCellDualStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ) (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (g : Langlands.GeneralLinear (t + 1) ℝ),
    additiveJacquetIntegral (-a) (ArchimedeanLocal.dualFunction (t + 1) f) g =
      ArchimedeanLocal.dualFunction (t + 1) (additiveJacquetIntegral a f) g

theorem realGodementOpenCellDual : RealGodementOpenCellDualStatement :=
  fun _ => additiveJacquetIntegral_dual

end Langlands.Global.RankinSelbergGlobal.RealGodement
