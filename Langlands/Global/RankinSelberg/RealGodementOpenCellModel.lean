import Langlands.Global.RankinSelberg.RealGodementOpenCellCovariance
import Langlands.Global.RankinSelberg.RealPrincipalSeriesSmoothCoefficient
import Langlands.Representation.Archimedean.RealLeviLimit

/-! # Real dominant-chamber Jacquet coefficients in the uniform Whittaker model -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory
open scoped BigOperators ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealInducedStandardBound RealPrincipalSeries

private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

variable {t : ℕ} {ds : List RealBlock}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "P" => principalSeries ℝ (t + 1) (realPositionCharacter ds)

/-- Evaluation at the identity of the convergent open-cell coefficient. -/
def additiveJacquetForm (a : ℝˣ) (hDom : IsStrictlyDominant (realPositionExponent ds) t) :
    P →ₗ[ℂ] ℂ :=
  LinearMap.proj (1 : G) ∘ₗ additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower ds) hDom

/-- The open-cell Jacquet form admits a compact derivative bound of order zero. -/
theorem hasCompactDerivativeBound_additiveJacquetForm (a : ℝˣ)
    (hDom : IsStrictlyDominant (realPositionExponent ds) t) :
    HasCompactDerivativeBound t ds (additiveJacquetForm a hDom) := by
  let e := fun j => (realPositionExponent ds j).re
  let F := expFun (t + 1) e
  have hF : F ∈ principalSeries ℝ (t + 1) (absChar e) := expFun_mem (t + 1) e
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hχF := RealLeviLimit.isSignedPower_absChar e
  have hDomF : IsStrictlyDominant (fun j => (e j : ℂ)) t := by
    intro j hj
    simpa only [Complex.ofReal_re, e] using hDom j hj
  have hFint := integrable_additiveJacquetKernel_of_mem_principalSeries a hχF hDomF hF (1 : G)
  let A := ∫ u : N, ‖additiveJacquetKernel a F 1 u‖ ∂upperStepHaar t a
  refine ⟨1, fun _ => [], A, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro f B hB
  have hPoint (x : G) : ‖f.val x‖ ≤ B 0 * ‖F x‖ := by
    obtain ⟨d, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
    have hFone : F k = 1 := by
      have h := expFun_mul (t + 1) e 1 hk
      simpa only [one_mul, expFun_one] using h
    have hEqNorm : ‖principalSeriesCharacter ℝ (t + 1) (absChar e) d‖ =
        ‖principalSeriesCharacter ℝ (t + 1) (realPositionCharacter ds) d‖ := by
      rw [norm_principalSeriesCharacter hχF, norm_principalSeriesCharacter hχ]
      simp only [Complex.ofReal_re, e]
    rw [f.property.2, hF.2, hFone, mul_one, norm_mul, hEqNorm, mul_comm (B 0)]
    exact mul_le_mul_of_nonneg_left (hB 0 k hk) (norm_nonneg _)
  have hPointKernel (u : N) : ‖additiveJacquetKernel a f 1 u‖ ≤ B 0 * ‖additiveJacquetKernel a F 1 u‖ := by
    simpa only [additiveJacquetKernel, norm_mul, norm_standardCharacter, mul_one] using
      hPoint (weylLong (t + 1) ℝ * u.val)
  have hfint := integrable_additiveJacquetKernel_of_mem_principalSeries a hχ hDom f.property (1 : G)
  change ‖∫ u : N, additiveJacquetKernel a f 1 u ∂upperStepHaar t a‖ ≤ A * ∑ i, B i
  rw [Fin.sum_univ_one]
  calc
    _ ≤ ∫ u : N, ‖additiveJacquetKernel a f 1 u‖ ∂upperStepHaar t a :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : N, B 0 * ‖additiveJacquetKernel a F 1 u‖ ∂upperStepHaar t a :=
      integral_mono hfint.norm (hFint.norm.const_mul (B 0)) hPointKernel
    _ = _ := by rw [integral_const_mul, mul_comm]

/-- The convergent open-cell coefficient as a linear map on the standard source. -/
def additiveJacquetUniformLinear (a : ℝˣ) (hDom : IsStrictlyDominant (realPositionExponent ds) t) :
    Automorphic.realStandardKFinite (t + 1) ds →ₗ[ℂ] (G → ℂ) :=
  functionalCoefficient ds (additiveJacquetForm a hDom)

theorem additiveJacquetUniformLinear_apply (a : ℝˣ) (hDom : IsStrictlyDominant (realPositionExponent ds) t)
    (f : Automorphic.realStandardKFinite (t + 1) ds) :
    additiveJacquetUniformLinear a hDom f = additiveJacquetIntegral a f.val := by
  funext g
  change additiveJacquetIntegral a (fun k => f.val (k * g)) 1 = additiveJacquetIntegral a f.val g
  rw [additiveJacquetIntegral_rightTranslate, one_mul]

theorem isRealUniformWhittakerIntertwiner_additiveJacquetUniformLinear (a : ℝˣ)
    (hDom : IsStrictlyDominant (realPositionExponent ds) t) :
    IsRealUniformWhittakerIntertwiner t ds (-a) (additiveJacquetUniformLinear a hDom) := by
  let L := additiveJacquetForm a hDom
  have hEquivariant (u : G) (hu : u ∈ GeneralLinear.upperUnipotent (t + 1) ℝ) (x : P) :
      L (translate t ds u x) = realWhittakerCharacter (-a) u * L x := by
    change additiveJacquetIntegral a (fun g => x.val (g * u)) 1 =
      realWhittakerCharacter (-a) u * additiveJacquetIntegral a x.val 1
    rw [additiveJacquetIntegral_rightTranslate, one_mul]
    simpa only [mul_one] using realGodementOpenCellCovariance t a x.val ⟨u, hu⟩ 1
  exact isRealUniformWhittakerIntertwiner_functionalCoefficient ds (-a) L
    (hasCompactDerivativeBound_additiveJacquetForm a hDom) hEquivariant

/-- The Jacquet coefficient of every standard K-finite vector in the dominant
chamber belongs to the uniform Whittaker model for the opposite phase. -/
def RealGodementOpenCellModelStatement : Prop :=
  ∀ (t : ℕ) (ds : List RealBlock) (a : ℝˣ),
    IsStrictlyDominant (realPositionExponent ds) t →
    ∀ f : Automorphic.realStandardKFinite (t + 1) ds,
      additiveJacquetIntegral a f.val ∈ realUniformWhittakerModel t ds (-a)

theorem realGodementOpenCellModel : RealGodementOpenCellModelStatement := by
  intro t ds a hDom f
  let C := additiveJacquetUniformLinear a hDom
  have hC := isRealUniformWhittakerIntertwiner_additiveJacquetUniformLinear a hDom
  have hle : LinearMap.range C ≤ realUniformWhittakerModel t ds (-a) :=
    le_iSup_of_le C (le_iSup_of_le hC le_rfl)
  exact hle ⟨f, additiveJacquetUniformLinear_apply a hDom f⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
