import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction
import Langlands.Representation.RankinSelberg.SegmentHeadGammaFactorProof
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.Classification.SegmentHeadContragredient

/-!
# Henniart's segment-head L, dual-L and gamma factor formulas

Henniart 2002, §2.6, printed page 595. The first display follows from the proved
JPSS Theorem (8.2) through the published reduction; the second display follows
from the first by smooth duality of segment heads and determinant-twist transport;
the third display is the published gamma double-product theorem.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData Classification.CuspidalProductContragredient

universe uF uV uW

/-- Henniart 2002, §2.6, first display, for arbitrary supplied segment heads: the
published reduction applied to the proved JPSS Theorem (8.2) at both universe
orders. -/
theorem segmentHeadLFactor : SegmentHeadLFactorStatement.{uF, uV, uW} :=
  segmentHeadLFactor_of_squareIntegrable squareIntegrableLFactor squareIntegrableLFactor

/-- Henniart's second segment-head L formula follows from his first one by
actual smooth duality and determinant-twist transport. -/
theorem segmentHeadContragredientLFactor_of_lFactor
    (h : SegmentHeadLFactorStatement.{uF, uV, uW}) :
    SegmentHeadContragredientLFactorStatement.{uF, uV, uW} := by
  intro p _ F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ.degree
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ'.degree
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ.rank
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup Δ'.rank
  let Av := twistedDualRep F.canonicalTopologicalData (-((Δ.length - 1 : ℕ) : ℝ)) A
  let Av' := twistedDualRep F.canonicalTopologicalData (-((Δ'.length - 1 : ℕ) : ℝ)) A'
  have hAv : Δ.dual.base.IsRepresentedBy Av := by
    change Av.isoClass = dualClass (Δ.base.twist ((Δ.length - 1 : ℕ) : ℝ))
    rw [dualClass_def]
    change Av.isoClass =
      F.canonicalTopologicalData.supercuspidalClassContragredient
        supercuspidalContragredient Δ.rank
        (F.canonicalTopologicalData.supercuspidalClassRealPowerTwist
          Δ.rank ((Δ.length - 1 : ℕ) : ℝ) Δ.base.cls)
    rw [classContragredient_realPowerTwist]
    simpa only [CuspidalDatum.IsRepresentedBy, CuspidalDatum.twist,
      dualDatum_cls, dualDatum_rank, Segment.rank] using
      (twistedDualRep_represents (-((Δ.length - 1 : ℕ) : ℝ)) hA)
  have hAv' : Δ'.dual.base.IsRepresentedBy Av' := by
    change Av'.isoClass = dualClass (Δ'.base.twist ((Δ'.length - 1 : ℕ) : ℝ))
    rw [dualClass_def]
    change Av'.isoClass =
      F.canonicalTopologicalData.supercuspidalClassContragredient
        supercuspidalContragredient Δ'.rank
        (F.canonicalTopologicalData.supercuspidalClassRealPowerTwist
          Δ'.rank ((Δ'.length - 1 : ℕ) : ℝ) Δ'.base.cls)
    rw [classContragredient_realPowerTwist]
    simpa only [CuspidalDatum.IsRepresentedBy, CuspidalDatum.twist,
      dualDatum_cls, dualDatum_rank, Segment.rank] using
      (twistedDualRep_represents (-((Δ'.length - 1 : ℕ) : ℝ)) hA')
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h p F ψ ν Δ.dual Δ'.dual
    π.contragredient σ.contragredient Av Av' hπ.contragredient hσ.contragredient hAv hAv'
  refine ⟨P, Q, hP, ?_, hPQ⟩
  intro j
  have hj := hQ j
  change IsPadicRankLPolynomial F ψ ν.val
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
      ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
        (-((Δ.length - 1 : ℕ) : ℝ)) (smoothContragredient A.obj.representation)))
    (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ'.rank)
      (-((Δ'.length - 1 : ℕ) : ℝ)) (smoothContragredient A'.obj.representation)) (Q j) at hj
  rw [← realPowerTwist_add, isPadicRankLPolynomial_realPowerTwist_move] at hj
  have hm : ((Δ.length - 1 : ℕ) : ℝ) = (Δ.length : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := Δ.length_pos; omega : 1 ≤ Δ.length)]
    norm_num
  have hm' : ((Δ'.length - 1 : ℕ) : ℝ) = (Δ'.length : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := Δ'.length_pos; omega : 1 ≤ Δ'.length)]
    norm_num
  have he : ((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ) +
      -((Δ.length - 1 : ℕ) : ℝ)) + -((Δ'.length - 1 : ℕ) : ℝ) =
        -((j : ℕ) : ℝ) := by
    rw [hm, hm']
    ring
  simpa only [he] using hj

/-- Henniart 2002, §2.6, second display, for arbitrary supplied segment heads. -/
theorem segmentHeadContragredientLFactor :
    SegmentHeadContragredientLFactorStatement.{uF, uV, uW} :=
  segmentHeadContragredientLFactor_of_lFactor segmentHeadLFactor

/-- Henniart 2002, §2.6, printed page 595: the two L-factor formulas and the
gamma-factor formula for pairs of segment heads. -/
theorem segmentHeadFactor : SegmentHeadFactorStatement.{uF, uV, uW} :=
  ⟨segmentHeadLFactor, segmentHeadContragredientLFactor, segmentHeadGammaFactor⟩

end Langlands.RankinSelberg
