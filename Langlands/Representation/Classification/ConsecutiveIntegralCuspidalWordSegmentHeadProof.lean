import Langlands.Representation.Classification.ConsecutiveIntegralCuspidalWordSegmentHeadStatement
import Langlands.Representation.Classification.IntegralCuspidalWordRealization
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.Representation.CuspidalSupport.TripleInductionMaps

/-! Identify the strong special head from an actual consecutive word. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

theorem consecutiveIntegralCuspidalWordSegmentHead :
    ConsecutiveIntegralCuspidalWordSegmentHead.{uF,uV} F T := by
  let := T.topology
  intro m hm A l hl a π hπi hπa hword
  classical
  let z : ℤ := a - ((l - 1 : ℕ) : ℤ)
  let D : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m) :=
    SupercuspidalRep.twist (T.determinantPowerCharacter m (z : ℝ))
      (T.isOpen_ker_determinantPowerCharacter m (z : ℝ))
      (T.ker_determinant_le_ker_determinantPowerCharacter m (z : ℝ)) A
  let Δ : Segment.{max uF uV, uF} T :=
    ⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m (z : ℝ) A.isoClass⟩, l, hl⟩
  let B := BlockShape.uniform l m hm
  let C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i) :=
    fun i => SupercuspidalRep.twist
      (T.determinantPowerCharacter m ((l - 1 - i.val : ℕ) : ℝ))
      (T.isOpen_ker_determinantPowerCharacter m _)
      (T.ker_determinant_le_ker_determinantPowerCharacter m _) D
  have hlabels (i : Fin B.length) :
      (⟨B.size i, (C i).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF}
          (F := F.Carrier) (n := d)) =
        ⟨m, T.supercuspidalClassRealPowerTwist m
          ((a - (i.val : ℤ) : ℤ) : ℝ) A.isoClass⟩ := by
    have hi : i.val ≤ l - 1 := by have := i.isLt; dsimp [B] at this; omega
    change (⟨m, T.supercuspidalClassRealPowerTwist m
      ((l - 1 - i.val : ℕ) : ℝ)
      (T.supercuspidalClassRealPowerTwist m (z : ℝ) A.isoClass)⟩ :
        Σ d : ℕ, SupercuspidalClass.{max uF uV, uF}
          (F := F.Carrier) (n := d)) = _
    rw [T.supercuspidalClassRealPowerTwist_add]
    congr 2
    push_cast
    rw [Nat.cast_sub hi]
    dsimp [z]
    push_cast
    ring
  have hocc := integralCuspidalJacquetWord_occurrence_of_labeling F T
    m (l * m) A B C (fun i => a - (i.val : ℤ)) π hlabels hword
  have hC := CuspidalSupport.glCuspidalTensor p F T (l * m)
    (Nat.mul_pos hl hm) B C
  obtain ⟨j, hj⟩ :=
    CuspidalSupport.exists_inductionInjection_of_cuspidalOccurrence F T B
      π (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
      hπi hπa hC.1 hC.2 hocc
  obtain ⟨P, hP, _⟩ := segmentSpecialConstituentExistence F T Δ
  have hD : Δ.base.IsRepresentedBy D := rfl
  obtain ⟨E⟩ := hP.nonempty_equiv_of_down_subrepresentation D hD hπi j hj
  have hhead := (T.isSegmentHead_iff Δ P D hD).mp hP
  exact (T.isSegmentHead_iff Δ π D hD).mpr (hhead.of_targetEquiv E.symm)

/-- The same identification at an arbitrary ambient rank, with the actual
word supplying the degree equality needed to transport the representation. -/
theorem consecutiveIntegralCuspidalWordSegmentHead_of_rank :
    letI := T.topology
    ∀ (m : ℕ) (hm : 0 < m)
      (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (l : ℕ) (hl : 0 < l) (a : ℤ) (n : ℕ)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible → π.IsAdmissible →
      IntegralCuspidalJacquetWord F T m n A π
        (List.ofFn (fun i : Fin l => a - (i.val : ℤ))) →
      ∃ h : l * m = n,
        T.IsSegmentHead
          (⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
            ((a - ((l - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩, l, hl⟩ :
              Segment.{max uF uV, uF} T)
          (h.symm ▸ π :
            SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (l * m) F.Carrier)) := by
  let := T.topology
  intro m hm A l hl a n π hπi hπa hw
  have hd : l * m = n := by
    simpa only [List.length_ofFn] using
      integralCuspidalJacquetWord_length_mul F T m n A π _ hw
  cases hd
  exact ⟨rfl, consecutiveIntegralCuspidalWordSegmentHead F T
    m hm A l hl a π hπi hπa hw⟩

end Langlands.Classification
