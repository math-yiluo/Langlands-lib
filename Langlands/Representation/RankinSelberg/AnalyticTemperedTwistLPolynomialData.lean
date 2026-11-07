import Langlands.Representation.RankinSelberg.AnalyticTemperedLFactor
import Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof

/-! Certified L-polynomials and their exact open disks after real twists. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial GeneralLinear
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

/-- The concrete two substitutions provided by unramified twist transport. -/
theorem realPowerTwistLPolynomial {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) (s z : ℝ) :
    IsPadicSymmetricLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) z σ)
      ((P.comp (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^
        (-(s : ℂ))) * X)).comp
          (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^
            (-(z : ℂ))) * X)) := by
  let T := F.canonicalTopologicalData
  have hχ (a : ℝ) (x : F.Carrierˣ) :
      (realPowerCharacter T.normalizedAbsUnits a x : ℂ) =
        (T.normalizedAbs (x : F.Carrier) : ℂ) ^ (a : ℂ) := by
    exact Complex.ofReal_cpow (T.normalizedAbs_nonneg _) a
  have hs := (unramifiedTwistLFactor p F ψ ν r t π σ
    (s : ℂ) (realPowerCharacter T.normalizedAbsUnits s) (hχ s) P hP).2
  exact (unramifiedTwistLFactor p F ψ ν r t
    (realPowerTwist (T.determinantNorm (r + 1)) s π) σ
    (z : ℂ) (realPowerCharacter T.normalizedAbsUnits z) (hχ z) _ hs).1

/-- Original-action twisted certificates, with the disk determined by the sum
of the two real exponents. -/
structure AnalyticTemperedTwistLPolynomialData (s z : ℝ) where
  polynomial : ℂ[X]
  spec : IsPadicSymmetricLPolynomial F ψ ν.val
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π)
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) z σ)
    polynomial
  poleFree : ∀ w : ℂ,
    ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (s + z) →
      polynomial.eval w ≠ 0

/-- Construct the twisted polynomial and disk bound from analytic temperedness,
with no polynomial or full Whittaker-type premise. -/
def analyticTemperedTwistLPolynomialData
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π)
    (hiσ : Representation.IsIrreducible σ)
    (htσ : F.canonicalTopologicalData.IsTempered σ)
    (s z : ℝ) : AnalyticTemperedTwistLPolynomialData F ψ ν π σ s z := by
  let d := analyticTemperedLPolynomialData F ψ ν π σ hiπ htπ hiσ htσ
  refine {
    polynomial := (d.polynomial.comp
      (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(s : ℂ))) * X)).comp
        (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(z : ℂ))) * X)
    spec := realPowerTwistLPolynomial F ψ ν π σ d.spec s z
    poleFree := ?_ }
  intro w hw
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  apply d.poleFree
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast lt_trans Nat.zero_lt_one
      F.canonicalTopologicalData.residueCardinality_gt_one
  have hn (a : ℝ) :
      ‖(F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(a : ℂ))‖ =
        q ^ (-a) := by
    rw [← Complex.ofReal_neg, Complex.norm_cpow_real, Complex.norm_natCast]
  rw [norm_mul, norm_mul, hn, hn, ← mul_assoc,
    ← Real.rpow_add hq, ← neg_add, Real.rpow_neg hq.le]
  exact (inv_mul_lt_one₀ (Real.rpow_pos_of_pos hq (s + z))).mpr hw

/-- Uniqueness transfers the exact disk bound to any certificate of the same
twisted pair. -/
theorem analyticTemperedTwistLPolynomial_poleFree
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π)
    (hiσ : Representation.IsIrreducible σ)
    (htσ : F.canonicalTopologicalData.IsTempered σ)
    (s z : ℝ) {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) z σ) P) :
    ∀ w : ℂ,
      ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (s + z) →
        P.eval w ≠ 0 := by
  let d := analyticTemperedTwistLPolynomialData F ψ ν π σ hiπ htπ hiσ htσ s z
  rw [hP.unique d.spec]
  exact d.poleFree

end Langlands.RankinSelberg
