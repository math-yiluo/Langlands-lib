import Langlands.Representation.RankinSelberg.SegmentHeadAnalyticLProduct
import Langlands.Representation.Classification.CenteredUnitarySegmentFamily

/-! # Actual analytic L-products for centered segment parameters -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial Classification

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance centeredAnalyticTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- The centered reciprocal-product identity using the lengths of the supplied
segment parameters. Certification of the actual actions is a separate input
to the theorem below. -/
def IsCenteredParameterLProduct {n m : ℕ}
    {π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear m F.Carrier)}
    (d : SquareIntegrableSegmentParameter F F.canonicalTopologicalData n π)
    (d' : SquareIntegrableSegmentParameter F F.canonicalTopologicalData m σ)
    (s t : ℝ) (P R : ℂ[X]) : Prop :=
  IsPadicShiftedReciprocalProduct F P
    (fun _ : Fin (min d.segment.length d'.segment.length) => R)
    (fun j => ((d.segment.length : ℝ) + d'.segment.length - 2) / 2 - (j : ℕ) + s + t)

private theorem realTwistedPolynomial_transport
    {a b n m : ℕ} (ha : a = n) (hb : b = m)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear m F.Carrier))
    (s t : ℝ) {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm m) t σ.representation) P) :
    IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm a) s
        (ha.symm ▸ π).representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm b) t
        (hb.symm ▸ σ).representation) P := by
  cases ha
  cases hb
  exact hP

/-- Actual segment heads, with the actual representatives of their midpoint
bases, have the centered shift formula after arbitrary real twists. -/
theorem reciprocal_of_midpointSegmentHeads_realTwists
    (hH : SegmentHeadLFactorStatement.{uF, uV, uW})
    (Δ : F.canonicalTopologicalData.Segment.{uV, uF})
    (Δ' : F.canonicalTopologicalData.Segment.{uW, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear Δ'.degree F.Carrier))
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := Δ'.rank))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ)
    (hA : (Δ.twist (((Δ.length : ℝ) - 1) / 2)).base.IsRepresentedBy A)
    (hA' : (Δ'.twist (((Δ'.length : ℝ) - 1) / 2)).base.IsRepresentedBy A')
    {R P : ℂ[X]}
    (hR : IsPadicRankLPolynomial F ψ ν.val A.obj.representation A'.obj.representation R)
    (s t : ℝ)
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.degree) s π.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ'.degree) t σ.representation) P)
    (z : ℂ) :
    (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality z))⁻¹ =
      ∏ j : Fin (min Δ.length Δ'.length),
        (R.eval (spectralPoint F.canonicalTopologicalData.residueCardinality
          (z + ((((Δ.length : ℝ) + Δ'.length - 2) / 2 - (j : ℕ) + s + t : ℝ) : ℂ))))⁻¹ := by
  let m : ℝ := ((Δ.length : ℝ) - 1) / 2
  let m' : ℝ := ((Δ'.length : ℝ) - 1) / 2
  let πc := F.canonicalTopologicalData.segmentFactor π m
  let σc := F.canonicalTopologicalData.segmentFactor σ m'
  have hπc : F.canonicalTopologicalData.IsSegmentHead (Δ.twist m) πc :=
    (segmentConstituentRealTwistCompatibility.{uF, uV}
      F F.canonicalTopologicalData Δ m π).2.1.mp hπ
  have hσc : F.canonicalTopologicalData.IsSegmentHead (Δ'.twist m') σc :=
    (segmentConstituentRealTwistCompatibility.{uF, uW}
      F F.canonicalTopologicalData Δ' m' σ).2.1.mp hσ
  have hPc : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.degree)
        (s - m) πc.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ'.degree)
        (t - m') σc.representation) P := by
    change IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist _ (s - m) (realPowerTwist _ m π.representation))
      (realPowerTwist _ (t - m') (realPowerTwist _ m' σ.representation)) P
    simpa only [← realPowerTwist_add, sub_add_cancel] using hP
  have he := reciprocal_of_segmentHeads_realTwists F ψ ν hH
    (Δ.twist m) (Δ'.twist m') πc σc A A' hπc hσc hA hA' hR
    (s - m) (t - m') hPc z
  rw [he]
  apply Finset.prod_congr rfl
  intro j _
  congr 3
  change z + (((Δ.length : ℝ) + Δ'.length - 2 - (j : ℕ) +
      (s - m) + (t - m') : ℝ) : ℂ) = _
  congr 1
  congr 1
  dsimp [m, m']
  ring

/-- The same centered product on the original square-integrable actions, with
the stored degree equalities transporting only the head witnesses. -/
theorem reciprocalProduct_of_squareIntegrableSegmentParameters
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uW})
    {n m : ℕ}
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear m F.Carrier))
    (d : SquareIntegrableSegmentParameter F F.canonicalTopologicalData n π)
    (d' : SquareIntegrableSegmentParameter F F.canonicalTopologicalData m σ)
    {R P : ℂ[X]}
    (hR : IsPadicRankLPolynomial F ψ ν.val
      d.base.obj.representation d'.base.obj.representation R)
    (s t : ℝ)
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π.representation)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm m) t σ.representation) P) :
    IsCenteredParameterLProduct F d d' s t P R := by
  intro z
  exact reciprocal_of_midpointSegmentHeads_realTwists F ψ ν hH
    d.segment d'.segment (d.degree_eq.symm ▸ π) (d'.degree_eq.symm ▸ σ)
    d.base d'.base d.head d'.head d.base_repr d'.base_repr hR s t
    (realTwistedPolynomial_transport F ψ ν d.degree_eq d'.degree_eq π σ s t hP) z

end Langlands.RankinSelberg
