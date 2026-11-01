import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankStatement
import Langlands.AlgebraicGeometry.Picard.FiniteFlatPullbackEulerLeadingCoefficientProof
import Langlands.AlgebraicGeometry.Picard.PolarizedTensorPowerEulerDilationProof

/-! # Native rank of a polarized finite-flat endomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- A polarized finite flat endomorphism has native rank equal to the
polarization factor raised to the relative dimension. -/
theorem polarizedFiniteFlatRank : PolarizedFiniteFlatRankStatement.{u} := by
  intro K _ _ X g hs hp hc f hf hflat L hample q hq he x
  obtain ⟨e⟩ := he
  obtain ⟨hL, P, hP, _, hPample⟩ := smoothProperLineBundleEulerPolynomial K X g hs hp hc L
  obtain ⟨hPd, hPc⟩ := hPample hample
  let Lf : LineBundle X.left := (LineBundle.pullback f.left).obj L
  obtain ⟨hF, Q, hQ, _, _⟩ := smoothProperLineBundleEulerPolynomial K X g hs hp hc Lf
  have hLC := finiteFlatPullbackEulerLeadingCoefficient K X g hs hp hc f hf hflat L hample hL hF P Q hP hQ x
  apply Langlands.Algebra.RationalPolynomial.scalar_eq_pow_of_eventually_nat_eval_dilation
    P Q q (f.left.finrank x) g
    (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hPc)) hPd hq ?_ hLC
  apply Filter.Eventually.of_forall
  intro n
  rw [hQ n, hP (q * n)]
  exact congrArg (Int.cast : ℤ → ℚ)
    ((polarizedTensorPowerEulerDilation.2 K X.left X.hom f.left L.obj q e n).2
      (hF n) (hL (q * n)))

end Langlands.AlgebraicGeometry.Picard
