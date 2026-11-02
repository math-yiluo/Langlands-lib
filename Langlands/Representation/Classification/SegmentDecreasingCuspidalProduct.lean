import Langlands.Representation.Classification.SegmentTensorStabilizerProof

/-! Actual decreasing cuspidal factors and their ordered one-twist separation. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual cuspidal factors of the existing decreasing segment induction,
together with their exact objects and ordered separation from a positive
one-twist of an earlier factor. -/
structure SegmentDecreasingCuspidalProductData {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (m : ℕ) (hr : 0 < r) where
  factors : letI := T.topology
    ∀ i : Fin (BlockShape.uniform m r hr).length,
      SupercuspidalRep.{uF,uV}
        (F := F.Carrier) (n := (BlockShape.uniform m r hr).size i)
  factors_eq : letI := T.topology
    (fun i => (factors i).obj) = T.segmentFactorsDown A.obj m hr
  product_eq : letI := T.topology
    (T.normalizedProductInductionFunctor.{uF,uV}
      (BlockShape.uniform m r hr)).obj (fun i => (factors i).obj) =
        T.segmentInducedDown A.obj m hr
  ordered_no_twist : letI := T.topology
    ∀ i j : Fin (BlockShape.uniform m r hr).length, i < j →
      (⟨(BlockShape.uniform m r hr).size j, (factors j).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{uV,uF}
          (F := F.Carrier) (n := d)) ≠
        ⟨(BlockShape.uniform m r hr).size i,
          T.supercuspidalClassRealPowerTwist
            ((BlockShape.uniform m r hr).size i) 1 (factors i).isoClass⟩

/-- Ordered decreasing integral twists avoid the obstruction
`later = ν earlier`, with `ν = |det|`. -/
theorem segmentSupercuspidalFactorsDown_ordered_no_twist {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    ∀ i j : Fin m, i < j →
      (⟨r, (segmentSupercuspidalFactor F T A
        ((m - 1 - j.val : ℕ) : ℝ)).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{uV,uF}
          (F := F.Carrier) (n := d)) ≠
        ⟨r, T.supercuspidalClassRealPowerTwist r 1
          (segmentSupercuspidalFactor F T A
            ((m - 1 - i.val : ℕ) : ℝ)).isoClass⟩ := by
  let := T.topology
  intro i j hij heq
  have hclass := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  let ρ : CuspidalDatum.{uV,uF} T := ⟨r, hr, A.isoClass⟩
  have hdatum : ρ.twist (((m - 1 - j.val : ℕ) : ℤ) : ℝ) =
      (ρ.twist (((m - 1 - i.val : ℕ) : ℤ) : ℝ)).twist 1 := by
    apply congrArg (CuspidalDatum.mk r hr)
    exact hclass
  rw [CuspidalDatum.twist_twist] at hdatum
  have hexp :
      ((m - 1 - j.val : ℕ) : ℤ) = 1 + ((m - 1 - i.val : ℕ) : ℤ) := by
    apply cuspidalDatum_integralTwist_injective F T ρ
    simpa only [Int.cast_add, Int.cast_one] using hdatum
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  omega

/-- Construct the actual decreasing cuspidal family without any derivative
or segment-constituent hypothesis. -/
def segmentDecreasingCuspidalProduct {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (m : ℕ) (hr : 0 < r) :
    SegmentDecreasingCuspidalProductData F T A m hr where
  factors i := segmentSupercuspidalFactor F T A ((m - 1 - i.val : ℕ) : ℝ)
  factors_eq := rfl
  product_eq := rfl
  ordered_no_twist := segmentSupercuspidalFactorsDown_ordered_no_twist F T A m hr

end Langlands.Classification
