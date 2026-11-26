import Langlands.Representation.RankinSelberg.CenteredSegmentFamilyLProduct
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo

/-! # Detecting supercuspidal discrete series by the self-pair at `-1` -/

noncomputable section

namespace Langlands.RankinSelberg

open Classification GeneralLinear HarmonicAnalysis LocalFactor Polynomial

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance discreteSelfPairTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance discreteSelfPairGroupTopology (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

private theorem spectralPoint_neg_one (q : ℕ) (hq : 0 < q) :
    spectralPoint q (-1) = (q : ℂ) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  rw [spectralPoint_eq_spectralParameter q hq']
  simpa [spectralParameter] using Complex.exp_log (Nat.cast_ne_zero.mpr hq.ne' : (q : ℂ) ≠ 0)

private theorem isSupercuspidal_of_cast {a b : ℕ} (h : a = b)
    (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    IsSupercuspidal ((h.symm ▸ π : SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear a F.Carrier))).representation → IsSupercuspidal π.representation := by
  cases h
  exact id

set_option maxHeartbeats 1300000 in
/-- For an irreducible square-integrable representation, a nonzero self-pair
Euler denominator at the residue cardinality forces segment length one. -/
theorem isSupercuspidal_of_squareIntegrable_selfPair_eval_ne_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} (hn : 0 < n)
    (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hi : π.IsIrreducible) (hsq : F.canonicalTopologicalData.IsSquareIntegrable π.representation)
    {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val π.representation
      (smoothContragredient π.representation) P)
    (hne : P.eval (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0) :
    IsSupercuspidal π.representation := by
  let T := F.canonicalTopologicalData
  let δ (_ : Unit) := π
  let d (i : Unit) : SquareIntegrableSegmentParameter F T n (δ i) :=
    squareIntegrableSegmentParameter F T n hn π hi hsq
  let D := centeredSegmentBaseEulerFamily supercuspidalEqualRankLFactor ψ ν d () ()
  have hbase : (1 : ℂ) ∈ D.data.parameters := D.one_mem_iff.mpr
    (isRankContragredient_dual_of_equiv _ _
      ((d ()).positiveBase_isSupercuspidal F T).1 rfl ⟨Representation.Equiv.refl _⟩)
  have hpole : D.data.reciprocal 0 = 0 := by
    change (D.data.denominator 0)⁻¹ = 0
    rw [D.data.denominator_zero hbase, inv_zero]
  have hlen : (d ()).segment.length = 1 := by
    by_contra he
    have hlen' : 2 ≤ (d ()).segment.length := by
      have := (d ()).segment.length_pos
      omega
    let j := (d ()).segment.length - 2
    have hj : j ∈ Finset.range (min ((d ()).segment.length - 1) ((d ()).segment.length - 1) + 1) := by
      rw [min_self, Finset.mem_range]
      dsimp [j]
      omega
    have hshift : Global.PoleComparison.blockShift
        (fun i => (d i).segment.length - 1) (fun _ => 0) () () j = 1 := by
      have hcast : (j : ℝ) = ((d ()).segment.length : ℝ) - 2 := by
        simp [j, Nat.cast_sub hlen']
      have hcast' : (((d ()).segment.length - 1 : ℕ) : ℝ) = ((d ()).segment.length : ℝ) - 1 := by
        simp [Nat.cast_sub (show 1 ≤ (d ()).segment.length by omega)]
      simp only [Global.PoleComparison.blockShift, hcast, hcast']
      ring
    let e := equivOfRepresentationEq (realPowerTwist_zero (T.determinantNorm n) π.representation).symm
    have hPt := (IsPadicRankLPolynomial.congr_equiv e (smoothContragredientEquiv e).symm).mp hP
    have heval := reciprocal_of_centeredSegment_mixedPair F ψ ν d
      (segmentHeadLFactor_of_squareIntegrable squareIntegrableLFactor squareIntegrableLFactor)
      supercuspidalEqualRankLFactor (fun _ => 0) () ()
      hPt (-1)
    have hzero : (P.eval (spectralPoint T.residueCardinality (-1)))⁻¹ = 0 := by
      rw [heval]
      apply Finset.prod_eq_zero hj
      rw [hshift]
      simpa using hpole
    exact hne (by
      rw [spectralPoint_neg_one _ (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one),
        inv_eq_zero] at hzero
      exact hzero)
  exact isSupercuspidal_of_cast F (d ()).degree_eq π
    (SegmentHeadDerivativeSupportLengthTwo.lengthOne_head_isSupercuspidal F T
      (d ()).segment hlen _ (d ()).head).2

end Langlands.RankinSelberg
