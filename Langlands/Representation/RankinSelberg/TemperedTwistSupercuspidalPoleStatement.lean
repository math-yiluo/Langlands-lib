import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Classification.Tempered

/-!
# A supercuspidal pair partner with a pole at `s = 0`

For an irreducible tempered representation `τ` of `GL_k(F)` and a real `u`, some
irreducible supercuspidal `ρ` of `GL_a(F)`, `a ≤ k`, makes `L(s, ν^u τ × ρ)` have
a pole at `s = 0`; `a < k` unless `τ` is supercuspidal. This is the step of
Henniart 2002, Théorème 1.6(b), (ii) ⇒ (i), that produces a pole from a block of
the Langlands datum, combining JPSS 1983, (8.1)(ii), (8.2) and (8.4).
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- Let `τ` be an irreducible tempered representation of `GL_k(F)`, `k ≥ 1`, and
`u` a real number. There are an irreducible supercuspidal representation `ρ` of
`GL_(r+1)(F)` with `r + 1 ≤ k`, and `r + 1 < k` when `τ` is not supercuspidal,
such that `L(s, ν^u τ × ρ) = 1 / P(q^(-s))` has a pole at `s = 0`: `P(1) = 0`.
Here `ν = |det|`. -/
def TemperedTwistSupercuspidalPoleStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (k : ℕ)
    (τ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear k F.Carrier))
    (u : ℝ),
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
        IsPadicRankLPolynomial F ψ ν.val
          (F.canonicalTopologicalData.segmentFactor τ u).representation
          ρ.representation P) ∧
      P.IsRoot 1

end Langlands.RankinSelberg
