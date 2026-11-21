import Langlands.Global.RankinSelberg.ComplexJacquetEvaluation
import Langlands.Global.RankinSelberg.ComplexLocalEqualSimpleRootBound
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursion

/-! # The simple-root estimate for canonical complex Jacquet coefficients -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GodementJacquet (traceCharacter)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure unipotentFourierSum)
open ComplexCompactProfileFamily (IsCompactProfile)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalConvergence (expDiagonal positiveLogSum simpleRootLogSum HasSimpleRootLogBound)
open ComplexLocalIwasawa (alpha alpha_iwasawa)
open ComplexLocalWhittakerGauge (logTorus)
open RealConvergenceAnalysis (rootPos rootPos_nonneg)

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "I" => Fin (r + 1)

/-- A slice of a uniform family satisfies the toral estimate with arbitrary real decay order. -/
theorem hasSimpleRootLogBound_of_uniform {P : Type*} {S : Set P} {W : P → G → ℂ}
    (hW : HasUniformSimpleRootBound S W) {p : P} (hp : p ∈ S) : HasSimpleRootLogBound (W p) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨(N : ℝ), Nat.cast_nonneg _, fun L _ => ?_⟩
  obtain ⟨J, hLJ⟩ := exists_nat_ge L
  obtain ⟨C, hC, hbound⟩ := hN J
  refine ⟨C, hC, fun x k => ?_⟩
  have hx : alpha (expDiagonal x * k.val) = x := by
    change alpha (logTorus x * k.val) = x
    simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 x k
  refine (hbound p hp _).trans ?_
  rw [hx, ComplexLocalConvergence.sum_abs_eq_positive_add_negative]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  change _ - (J : ℝ) * rootPos x ≤ _ - L * rootPos x
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hLJ (rootPos_nonneg x)) _

/-- The canonical continuation gives a valid smaller coefficient for the quotient recursion. -/
def ComplexJacquetCanonicalBoundsStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ)
    (φ : Matrix.unitaryGroup I ℂ → ℂ) (hφ : IsCompactProfile l φ) (p : I → ℂ),
    let W := canonicalJacquetFamily μ a l φ hφ p
    Continuous W ∧
      (∀ (u : U) (g : G), W (u.val * g) = traceCharacter (-a) (unipotentFourierSum r u) * W g) ∧
      HasSimpleRootLogBound W

theorem complexJacquetCanonicalBounds : ComplexJacquetCanonicalBoundsStatement (r := r) := by
  intro μ a l φ hφ p
  have hW := canonicalJacquetFamily_properties μ a l φ hφ
  obtain ⟨δ, hδ, hB⟩ := hW.2.2.1 p
  exact ⟨hW.1 p, canonicalJacquetFamily_left_mul μ a l φ hφ p,
    hasSimpleRootLogBound_of_uniform hB (Metric.mem_ball_self hδ)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
