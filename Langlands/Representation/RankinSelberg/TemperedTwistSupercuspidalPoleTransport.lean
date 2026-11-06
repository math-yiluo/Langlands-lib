import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleStatement
import Langlands.Representation.RankinSelberg.RankOneTestReduction

/-!
# Removing the real twist from supercuspidal pole existence

Opposite real determinant twists preserve the complete pair L-polynomial.
Consequently the tempered pole-existence target reduces to its untwisted case.
The latter remains an explicit hypothesis.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- Opposite real determinant twists preserve the actual pair L-polynomial,
including for the arbitrary-rank interface. -/
theorem isPadicRankLPolynomial_realPowerTwist
    {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (u : ℝ) (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) u π)
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) (-u) σ) P ↔
      IsPadicRankLPolynomial F ψ ν π σ P := by
  cases n with
  | zero => rfl
  | succ n =>
    cases t with
    | zero => rfl
    | succ t =>
      have hc (l : ℕ) (s : ℝ) :
          realPowerCharacter (F.canonicalTopologicalData.determinantNorm l) s =
            (realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s).comp
              determinant := rfl
      simpa only [IsPadicRankLPolynomial, realPowerTwist, hc, realPowerCharacter_neg] using
        isPadicSymmetricLPolynomial_twist ψ ν π σ
          (realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits u) P

/-- The untwisted case of `TemperedTwistSupercuspidalPoleStatement`.
It retains both rank bounds and the independent partner universe. -/
def UntwistedTemperedSupercuspidalPoleStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (k : ℕ)
    (τ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear k F.Carrier)),
    0 < k →
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible τ.representation) →
    (letI := F.canonicalTopologicalData.topology;
      F.canonicalTopologicalData.IsTempered τ.representation) →
    ∃ (r : ℕ) (ρ : letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)) (P : ℂ[X]),
      (letI := F.canonicalTopologicalData.topology;
        Representation.IsIrreducible ρ.representation) ∧
      (letI := F.canonicalTopologicalData.topology;
        GeneralLinear.IsSupercuspidal ρ.representation) ∧
      r + 1 ≤ k ∧
      (¬ (letI := F.canonicalTopologicalData.topology;
        GeneralLinear.IsSupercuspidal τ.representation) → r + 1 < k) ∧
      (letI := F.canonicalTopologicalData.topology;
        IsPadicRankLPolynomial F ψ ν.val τ.representation ρ.representation P) ∧
      P.IsRoot 1

/-- Move the inverse real determinant twist to the partner. The untwisted
pole-existence assertion is the only hypothesis. -/
theorem temperedTwistSupercuspidalPole_of_untwisted
    (h : UntwistedTemperedSupercuspidalPoleStatement.{uF, uV, uW}) :
    TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW} := by
  intro p _ F ψ ν k τ u hk hτ ht
  let := F.canonicalTopologicalData.topology
  obtain ⟨r, ρ, P, hρ, hρs, hr, hstrict, hP, hroot⟩ := h p F ψ ν k τ hk hτ ht
  refine ⟨r, F.canonicalTopologicalData.segmentFactor ρ (-u), P, ?_, ?_,
    hr, hstrict, ?_, hroot⟩
  · exact (SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ
  · exact (GeneralLinear.isSupercuspidal_twist_iff _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (r + 1) (-u))
      (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter
        (r + 1) (-u)) ρ.representation).mpr hρs
  · exact (isPadicRankLPolynomial_realPowerTwist ψ ν.val
      τ.representation ρ.representation u P).mpr hP

/-- The full real-twist target is equivalent to its untwisted case. -/
theorem temperedTwistSupercuspidalPole_iff_untwisted :
    TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW} ↔
      UntwistedTemperedSupercuspidalPoleStatement.{uF, uV, uW} := by
  refine ⟨?_, temperedTwistSupercuspidalPole_of_untwisted⟩
  intro h p _ F ψ ν k τ hk hτ ht
  let := F.canonicalTopologicalData.topology
  obtain ⟨r, ρ, P, hρ, hρs, hr, hstrict, hP, hroot⟩ := h p F ψ ν k τ 0 hk hτ ht
  refine ⟨r, ρ, P, hρ, hρs, hr, hstrict, ?_, hroot⟩
  change IsPadicRankLPolynomial F ψ ν.val
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm k) 0 τ.representation)
    ρ.representation P at hP
  simpa only [realPowerTwist_zero] using hP

end Langlands.RankinSelberg
