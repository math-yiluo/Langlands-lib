import Langlands.Representation.Aubert.QuasicuspidalJacquetExchange
import Langlands.Representation.Smooth.CentralSignedClassTransfer
import Langlands.Representation.Classification.SegmentJacquetSubobject
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SegmentFullJacquetAdjunction

/-! Actual head identification from a signed reversed segment Jacquet class. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Classification SegmentFullJacquet Parabolic CuspidalSupport
open OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual reversed full cuspidal Jacquet object of a segment
subrepresentation has a centrally separated simple series. -/
theorem exists_segmentReversedJacquetSeries
    {Δ : T.Segment.{uV,uF}}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    letI := T.topology
    let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
    ∃ (N : ℕ) (s : ObjectRepFiltration (reversedJacquetObject F T B π).obj N)
      (z : B.Levi F.Carrier) (c : Fin N → ℂ),
      s.HasSimpleFactors ∧ (∀ g, z * g = g * z) ∧ Function.Injective c ∧
        ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v := by
  let := T.topology
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  let J := (T.normalizedJacquetFunctor B).obj π
  obtain ⟨N, s, c, hs, hc, hgr⟩ :=
    exists_subrepresentationJacquetSeries F T π hπ A hA
  let e : B.Levi F.Carrier ≃* B.Levi F.Carrier := leviReverseEquiv B
  let z := separatingScalar F T Δ.length Δ.rank Δ.rank_pos
  obtain ⟨t, ht, htgr⟩ :=
    CentralEigenspaceSplitting.exists_scalarSeries_pullback e s hs z c hgr
  have hz := CentralEigenspaceSplitting.groupEquiv_central e z
    (separatingScalar_comm F T Δ.length Δ.rank Δ.rank_pos)
  change ∃ (N : ℕ)
    (s : ObjectRepFiltration
      (SmoothRep.pullback (outerReverseLeviEquivContinuous B F.Carrier)
        ((T.normalizedJacquetFunctor B.reverse).obj π)).obj N)
    (z : B.Levi F.Carrier) (c : Fin N → ℂ),
    s.HasSimpleFactors ∧ (∀ g, z * g = g * z) ∧ Function.Injective c ∧
      ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v
  rw [uniformJacquetObject_reverse_eq F T Δ.rank_pos π]
  exact ⟨N, t, e.symm z, c, ht, hz, hc, htgr⟩

/-- A signed equality between the actual upper Jacquet class of an irreducible
and the reversed Jacquet class of a segment subrepresentation forces the
positive sign and identifies that irreducible with the supplied special head.
This result does not supply the signed class equality or the irreducible. -/
theorem segmentHead_of_signedJacquetClass
    (Δ : T.Segment.{max uF uV,uF})
    (πZ πS τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSubrepresentation Δ πZ) (hS : T.IsSegmentHead Δ πS)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hEq : letI := T.topology
      let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
      let hZfl := SmoothRep.hasFiniteLength_of_isIrreducible (by
        obtain ⟨_, _, h⟩ := hZ
        exact h.1)
      B.finiteLengthClass F.Carrier ((T.normalizedJacquetFunctor B).obj τ)
          (normalizedJacquetK0_hasFiniteLength F T B τ
            (SmoothRep.hasFiniteLength_of_isIrreducible hτ)) =
        ε • B.finiteLengthClass F.Carrier (reversedJacquetObject F T B πZ)
          (reversedJacquetObject_hasFiniteLength F T B πZ hZfl)) :
    letI := T.topology
    ε = 1 ∧ Nonempty (τ.representation.Equiv πS.representation) := by
  let := T.topology
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  obtain ⟨A, hA, hZi, j, hj⟩ := hZ
  have hZ' : T.IsSegmentSubrepresentation Δ πZ := ⟨A, hA, hZi, j, hj⟩
  have hj0 : j ≠ 0 := by
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hZi
    intro h
    apply hv
    apply hj
    rw [h, map_zero]
    rfl
  obtain ⟨f, hf⟩ := exists_jacquet_to_tensor_ne_zero F T Δ.rank_pos A.obj πZ j hj0
  obtain ⟨g, hg⟩ := exists_reversedJacquet_to_segmentTensorDown_ne_zero
    F T Δ.rank_pos A.obj πZ f hf
  let R := reversedJacquetObject F T B πZ
  let J := (T.normalizedJacquetFunctor B).obj τ
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)
  have hR : R.HasFiniteLength := reversedJacquetObject_hasFiniteLength F T B πZ
    (SmoothRep.hasFiniteLength_of_isIrreducible hZi)
  have hJ : J.HasFiniteLength := normalizedJacquetK0_hasFiniteLength F T B τ
    (SmoothRep.hasFiniteLength_of_isIrreducible hτ)
  have hσ : σ.IsIrreducible :=
    (segmentFactorsDown_isIrreducible_isLeviCuspidal F T
      Δ.length Δ.length_pos Δ.rank_pos A).1
  obtain ⟨N, s, z, c, hs, hz, hc, hgr⟩ :=
    exists_segmentReversedJacquetSeries F T πZ hZ' A hA
  obtain ⟨hεone, q, hq⟩ := SmoothRep.signedClass_eq_one_and_exists_surjective
    R J σ hR hJ hσ s hs z hz c hc hgr ε hε hEq g hg
  have hq0 : q ≠ 0 := by
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hσ
    obtain ⟨w, hw⟩ := hq v
    intro h
    apply hv
    rw [h] at hw
    exact hw.symm
  exact ⟨hεone, hS.nonempty_equiv_of_down_jacquet_hom A hA hτ q hq0⟩

/-- Choose the actual special-head equivalence established by the signed
Jacquet class test. All class and irreducibility premises remain explicit. -/
def segmentHeadEquivOfSignedJacquetClass
    (Δ : T.Segment.{max uF uV,uF})
    (πZ πS τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSubrepresentation Δ πZ) (hS : T.IsSegmentHead Δ πS)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hEq : letI := T.topology
      let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
      let hZfl := SmoothRep.hasFiniteLength_of_isIrreducible (by
        obtain ⟨_, _, h⟩ := hZ
        exact h.1)
      B.finiteLengthClass F.Carrier ((T.normalizedJacquetFunctor B).obj τ)
          (normalizedJacquetK0_hasFiniteLength F T B τ
            (SmoothRep.hasFiniteLength_of_isIrreducible hτ)) =
        ε • B.finiteLengthClass F.Carrier (reversedJacquetObject F T B πZ)
          (reversedJacquetObject_hasFiniteLength F T B πZ hZfl)) :
    letI := T.topology
    τ.representation.Equiv πS.representation :=
  Classical.choice (segmentHead_of_signedJacquetClass F T Δ πZ πS τ
    hZ hS hτ ε hε hEq).2

end Langlands.Aubert
