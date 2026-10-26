import Langlands.Representation.Classification.SegmentTensorStabilizerStatement
import Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof

/-! Integral members and actual inducing tensors of a segment are distinct. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Integral twists of an actual positive-rank cuspidal datum are distinct. -/
theorem cuspidalDatum_integralTwist_injective (ρ : CuspidalDatum.{uV,uF} T) :
    Function.Injective (fun k : ℤ => ρ.twist (k : ℝ)) := by
  intro i j hij
  have hz : ρ.twist ((i - j : ℤ) : ℝ) = ρ := by
    calc
      _ = (ρ.twist (i : ℝ)).twist (-(j : ℝ)) := by
        rw [CuspidalDatum.twist_twist]
        congr 1
        push_cast
        ring
      _ = (ρ.twist (j : ℝ)).twist (-(j : ℝ)) :=
        congrArg (fun d => d.twist (-(j : ℝ))) hij
      _ = ρ := by rw [CuspidalDatum.twist_twist, neg_add_cancel, CuspidalDatum.twist_zero]
  exact sub_eq_zero.mp ((cuspidalIntegralTwistFreeness F T ρ (i - j)).mp hz)

/-- Natural-indexed members of a segment never repeat. -/
theorem segment_member_injective (Δ : Segment.{uV,uF} T) :
    Function.Injective Δ.member := by
  intro i j hij
  have h : (i : ℤ) = (j : ℤ) :=
    cuspidalDatum_integralTwist_injective F T Δ.base (by simpa [Segment.member] using hij)
  exact_mod_cast h

/-- The actual supercuspidal representative of one determinant-power factor. -/
def segmentSupercuspidalFactor {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) (s : ℝ) :
    letI := T.topology
    SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter r s)
    (T.isOpen_ker_determinantPowerCharacter r s)
    (T.ker_determinant_le_ker_determinantPowerCharacter r s) A

/-- Its smooth object is precisely the existing segment factor. -/
theorem segmentSupercuspidalFactor_obj {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) (s : ℝ) :
    letI := T.topology
    (segmentSupercuspidalFactor F T A s).obj = T.segmentFactor A.obj s := rfl

/-- The actual cuspidal data of factors with distinct integral indices are distinct. -/
theorem segmentSupercuspidalFactor_datum_injective {r m : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (e : Fin m → ℤ) (he : Function.Injective e) :
    letI := T.topology
    Function.Injective (fun i =>
      (⟨r, hr, (segmentSupercuspidalFactor F T A (e i : ℝ)).isoClass⟩ :
        CuspidalDatum.{uV,uF} T)) := by
  let := T.topology
  change Function.Injective (fun i =>
    (⟨r, hr, A.isoClass⟩ : CuspidalDatum.{uV,uF} T).twist (e i : ℝ))
  exact (cuspidalDatum_integralTwist_injective F T _).comp he

/-- The actual tensor of integrally indexed segment factors has trivial
minimal self-association stabilizer whenever the indices are distinct. -/
theorem segmentTensorStabilizer_count {r m : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (e : Fin m → ℤ) (he : Function.Injective e) :
    letI := T.topology
    Nat.card (CuspidalSupport.AssociatingPermutations
      (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
      (FiniteTensor.external (fun i =>
        (segmentSupercuspidalFactor F T A (e i : ℝ)).obj.representation))
      (FiniteTensor.external (fun i =>
        (segmentSupercuspidalFactor F T A (e i : ℝ)).obj.representation))) = 1 := by
  let := T.topology
  exact CuspidalSupport.distinctCuspidalTensorStabilizer_count F T
    (BlockShape.uniform m r hr) (fun i => segmentSupercuspidalFactor F T A (e i : ℝ))
    (segmentSupercuspidalFactor_datum_injective F T hr A e he)

/-- Natural indices give distinct actual cuspidal factor data. -/
theorem segmentSupercuspidalFactor_datum_injective_nat {r m : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
    (e : Fin m → ℕ) (he : Function.Injective e) :
    letI := T.topology
    Function.Injective (fun i =>
      (⟨r, hr, (segmentSupercuspidalFactor F T A (e i : ℝ)).isoClass⟩ :
        CuspidalDatum.{uV,uF} T)) := by
  let := T.topology
  change Function.Injective (fun i =>
    (⟨r, hr, A.isoClass⟩ : CuspidalDatum.{uV,uF} T).twist (e i : ℝ))
  intro i j hij
  apply he
  apply Int.ofNat_inj.mp
  apply cuspidalDatum_integralTwist_injective F T (⟨r, hr, A.isoClass⟩ : CuspidalDatum T)
  simpa only [Int.cast_natCast] using hij

/-- Exact self-association count for the increasing inducing tensor. -/
theorem segmentFactors_tensorStabilizer_count {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    Nat.card (CuspidalSupport.AssociatingPermutations
      (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
      (FiniteTensor.external (fun i => (T.segmentFactors A.obj m hr i).representation))
      (FiniteTensor.external (fun i => (T.segmentFactors A.obj m hr i).representation))) = 1 := by
  let := T.topology
  exact CuspidalSupport.distinctCuspidalTensorStabilizer_count F T
    (BlockShape.uniform m r hr)
    (fun i => segmentSupercuspidalFactor F T A (i.val : ℝ))
    (segmentSupercuspidalFactor_datum_injective_nat F T hr A Fin.val Fin.val_injective)

/-- Exact self-association count for the decreasing inducing tensor. -/
theorem segmentFactorsDown_tensorStabilizer_count {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    Nat.card (CuspidalSupport.AssociatingPermutations
      (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
      (FiniteTensor.external (fun i => (T.segmentFactorsDown A.obj m hr i).representation))
      (FiniteTensor.external (fun i => (T.segmentFactorsDown A.obj m hr i).representation))) = 1 := by
  let := T.topology
  have he : Function.Injective (fun i : Fin m => m - 1 - i.val) := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hij
    omega
  exact CuspidalSupport.distinctCuspidalTensorStabilizer_count F T
    (BlockShape.uniform m r hr)
    (fun i => segmentSupercuspidalFactor F T A ((m - 1 - i.val : ℕ) : ℝ))
    (segmentSupercuspidalFactor_datum_injective_nat F T hr A _ he)

/-- The actual increasing tensor is irreducible and cuspidal on its Levi. -/
theorem segmentFactors_isIrreducible_isLeviCuspidal {r : ℕ} (m : ℕ)
    (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
    σ.IsIrreducible ∧
      CuspidalSupport.IsLeviCuspidal (BlockShape.uniform m r hr) σ.representation := by
  let := T.topology
  exact CuspidalSupport.glCuspidalTensor p F T (m * r) (Nat.mul_pos hm hr)
    (BlockShape.uniform m r hr)
    (fun i => segmentSupercuspidalFactor F T A (i.val : ℝ))

/-- The actual decreasing tensor is irreducible and cuspidal on its Levi. -/
theorem segmentFactorsDown_isIrreducible_isLeviCuspidal {r : ℕ} (m : ℕ)
    (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    let τ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)
    τ.IsIrreducible ∧
      CuspidalSupport.IsLeviCuspidal (BlockShape.uniform m r hr) τ.representation := by
  let := T.topology
  exact CuspidalSupport.glCuspidalTensor p F T (m * r) (Nat.mul_pos hm hr)
    (BlockShape.uniform m r hr)
    (fun i => segmentSupercuspidalFactor F T A ((m - 1 - i.val : ℕ) : ℝ))

/-- Exact grouped premise for the actual increasing and decreasing segment tensors. -/
theorem segmentTensorStabilizerAndCuspidality :
    SegmentTensorStabilizerAndCuspidality.{uF,uV} F T := by
  let := T.topology
  intro r m hr A
  refine ⟨segmentFactors_tensorStabilizer_count F T m hr A,
    segmentFactorsDown_tensorStabilizer_count F T m hr A, ?_⟩
  intro hm
  exact ⟨segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A,
    segmentFactorsDown_isIrreducible_isLeviCuspidal F T m hm hr A⟩

end Langlands.Classification
