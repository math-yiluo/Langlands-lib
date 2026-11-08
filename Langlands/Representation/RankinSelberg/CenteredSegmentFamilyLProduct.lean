import Langlands.Representation.RankinSelberg.CenteredSegmentAnalyticLProduct
import Langlands.Representation.RankinSelberg.CenteredSegmentBaseEuler
import Langlands.Representation.Classification.CenteredUnitarySegmentDual
import Langlands.Representation.Classification.TwistedProductOrdinaryDualProof
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction

/-! # The Appendix L-product from actual mixed segment pairs -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial Classification

universe uF uV uI

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance centeredFamilyTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance centeredFamilyGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

private theorem dualPairPolynomial_transport
    {r t a b : ℕ} (hr : r = a) (ht : t = b)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear t F.Carrier))
    {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (F.canonicalTopologicalData.castRank hr A).representation
      (smoothContragredient
        (F.canonicalTopologicalData.castRank ht B).representation) P) :
    IsPadicRankLPolynomial F ψ ν.val A.representation
      (smoothContragredient B.representation) P := by
  cases hr
  cases ht
  exact hP

variable {I : Type uI} {n : I → ℕ}
  {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
  (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i))

/-- The Euler polynomial of the positive-rank notation also certifies the
actual chosen bases at their original ranks. -/
theorem centeredSegmentBaseEulerFamily_certified
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (i j : I) :
    IsPadicRankLPolynomial F ψ ν.val
      (d i).base.obj.representation (smoothContragredient (d j).base.obj.representation)
      (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.polynomial := by
  exact dualPairPolynomial_transport F ψ ν
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (d i).segment.rank_pos)).symm
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (d j).segment.rank_pos)).symm
    (d i).base.obj (d j).base.obj
    (centeredSegmentBaseEulerFamily hEq ψ ν d i j).certified

/-- A certified polynomial has precisely the Appendix L-product for the
lengths, exponents and actual base Euler functions of the supplied family. -/
def IsCenteredSegmentFamilyLProduct [Fintype I]
    (s : I → ℝ) (P : ℂ[X]) (base : I → I → ℂ → ℂ) : Prop :=
  ∀ z : ℂ,
    (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹ =
      Global.PoleComparison.blockLFactor (fun i => (d i).segment.length - 1) s base z

private theorem min_length_sub_add_one (i j : I) :
    min ((d i).segment.length - 1) ((d j).segment.length - 1) + 1 =
      min (d i).segment.length (d j).segment.length := by
  have hi := (d i).segment.length_pos
  have hj := (d j).segment.length_pos
  omega

/-- Each actual twisted block paired with the actual smooth dual of another
twisted block has the Appendix shift, using the chosen base Euler polynomial. -/
theorem reciprocal_of_centeredSegment_mixedPair
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (s : I → ℝ) (i j : I) {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
        (s i) (δ i).representation)
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)) P)
    (z : ℂ) :
    (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹ =
      ∏ k ∈ Finset.range
          (min ((d i).segment.length - 1) ((d j).segment.length - 1) + 1),
        (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal
          (z + (Global.PoleComparison.blockShift
            (fun i => (d i).segment.length - 1) s i j k : ℂ)) := by
  let E := centeredSegmentBaseEulerFamily hEq ψ ν d i j
  have hPt : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
        (s i) (δ i).representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
        (-s j) (δ j).contragredient.representation) P :=
    (IsPadicRankLPolynomial.congr_equiv
      (Representation.Equiv.refl _)
      (segmentFactorSmoothDualEquiv F F.canonicalTopologicalData (δ j) (s j))).mp hP
  have he := reciprocalProduct_of_squareIntegrableSegmentParameters F ψ ν hH
    (δ i) (δ j).contragredient (d i) ((d j).contragredient F F.canonicalTopologicalData)
    (centeredSegmentBaseEulerFamily_certified F ψ ν d hEq i j) (s i) (-s j) hPt z
  rw [he, Finset.prod_range, min_length_sub_add_one F d i j]
  apply Finset.prod_congr rfl
  intro k _
  rw [E.reciprocal_eq_of_certified E.certified]
  congr 3
  congr 1
  have hi : (((d i).segment.length - 1 : ℕ) : ℝ) =
      ((d i).segment.length : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := (d i).segment.length_pos; omega : 1 ≤ (d i).segment.length)]
    norm_num
  have hj : (((d j).segment.length - 1 : ℕ) : ℝ) =
      ((d j).segment.length : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := (d j).segment.length_pos; omega : 1 ≤ (d j).segment.length)]
    norm_num
  simp only [Global.PoleComparison.blockShift, hi, hj]
  congr 1
  change ((↑(d i).segment.length + ↑(d j).segment.length - 2) / 2 -
    ↑(k : ℕ) + s i + -s j : ℝ) = _
  ring

/-- Pair certificates and their exact polynomial product identify the whole
mixed product with the Appendix function. -/
theorem centeredSegmentFamilyLProduct_of_certifiedProduct [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (s : I → ℝ) {P : ℂ[X]} (Q : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
        (s i) (δ i).representation)
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)) (Q i j))
    (hprod : P = ∏ i, ∏ j, Q i j) :
    IsCenteredSegmentFamilyLProduct F d s P
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  intro z
  rw [hprod, eval_prod]
  simp only [eval_prod, ← Finset.prod_inv_distrib]
  unfold Global.PoleComparison.blockLFactor
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact reciprocal_of_centeredSegment_mixedPair F ψ ν d hH hEq s i j (hQ i j) z

end Langlands.RankinSelberg
