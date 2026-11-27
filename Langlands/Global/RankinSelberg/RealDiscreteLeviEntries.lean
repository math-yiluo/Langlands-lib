import Langlands.Global.RankinSelberg.RealDiscreteLeviDeformation
import Langlands.Global.RankinSelberg.RealDiscreteLeviInner
import Langlands.Representation.Archimedean.RealLeviLeviBorel

/-! # Lower Levi entries of the real nonzero-weight slots -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviEntries

open RealInducedBlockBound RealInducedStandardBound RealDiscreteLeviDeformation
open RealLeviLeviBorel RealDiscreteLeviFourier

/-- The induced slots with nonzero weight in their original order. -/
def discreteSlots (ds : List RealBlock) (n : ℕ) : List (Slot n) :=
  (slots ds n).filter fun s => s.M ≠ 0

theorem mem_discreteSlots {ds : List RealBlock} {n : ℕ} {s : Slot n} :
    s ∈ discreteSlots ds n ↔ s ∈ slots ds n ∧ s.M ≠ 0 := by
  simp [discreteSlots]

theorem pairwise_discreteSlots (ds : List RealBlock) (n : ℕ) :
    (discreteSlots ds n).Pairwise Slot.Disjoint :=
  (pairwise_slots ds n).sublist List.filter_sublist

variable {n : ℕ} (ds : List RealBlock)

local notation "L" => discreteSlots ds n
local notation "cl" => fun i : Fin n => blockStart ds i

private theorem start_eq_of_slot {s : Slot n} (hs : s ∈ L) :
    blockStart ds (s.p + 1) = blockStart ds s.p := by
  obtain ⟨hm, hw⟩ := mem_discreteSlots.mp hs
  obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hm
  exact (blockStart_succ_eq_iff ds p).2 ⟨d, hd, Int.natAbs_ne_zero.mp hw⟩

private def slotEntry (i : Fin (L).length) : CoordM cl :=
  let s := (L).get i
  ⟨(⟨s.p + 1, s.hp⟩, ⟨s.p, Nat.lt_of_succ_lt s.hp⟩),
    start_eq_of_slot ds (List.get_mem L i), Nat.lt_succ_self _⟩

private theorem slotEntry_injective : Function.Injective (slotEntry (n := n) ds) := by
  intro i j h
  have hp := congrArg (fun p : CoordM cl => p.val.2.val) h
  change ((L).get i).p = ((L).get j).p at hp
  rcases lt_trichotomy i j with hij | h | hji
  · have hd := List.pairwise_iff_get.1 (pairwise_discreteSlots ds n) i j hij
    rcases hd with hd | hd <;> omega
  · exact h
  · have hd := List.pairwise_iff_get.1 (pairwise_discreteSlots ds n) j i hji
    rcases hd with hd | hd <;> omega

/-- Each within-class lower coordinate is the simple entry of one nonzero-weight slot. -/
theorem coordM_adjacent (p : CoordM cl) : p.val.2.val + 1 = p.val.1.val := by
  have h₀ := le_blockStart ds p.val.1
  have h₁ := blockStart_le ds p.val.2
  have he := p.property.1
  change blockStart ds p.val.1 = blockStart ds p.val.2 at he
  have hlt := Fin.lt_def.mp p.property.2
  omega

private theorem slotEntry_surjective : Function.Surjective (slotEntry (n := n) ds) := by
  intro p
  have hsucc := coordM_adjacent ds p
  have hp : p.val.2.val + 1 < n := hsucc ▸ p.val.1.isLt
  have hEq : blockStart ds (p.val.2.val + 1) = blockStart ds p.val.2 := hsucc ▸ p.property.1
  obtain ⟨d, hd, hw⟩ := (blockStart_succ_eq_iff ds p.val.2).1 hEq
  let s := mkSlot ds n p.val.2 hp d
  have hs : s ∈ L := mem_discreteSlots.mpr ⟨mkSlot_mem_slots hd hp, Int.natAbs_ne_zero.mpr hw⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hs
  refine ⟨i, Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_))⟩
  · change ((L).get i).p + 1 = p.val.1.val
    rw [hi]
    exact hsucc
  · change ((L).get i).p = p.val.2.val
    rw [hi]
    rfl

/-- Identify the lower Levi coordinates with the nonzero-weight slots. -/
def entryEquiv : Fin (L).length ≃ CoordM cl :=
  Equiv.ofBijective (slotEntry ds) ⟨slotEntry_injective ds, slotEntry_surjective ds⟩

theorem entryEquiv_row (i : Fin (L).length) :
    (entryEquiv ds i).val.1.val = ((L).get i).p + 1 := rfl

theorem entryEquiv_col (i : Fin (L).length) :
    (entryEquiv ds i).val.2.val = ((L).get i).p := rfl

/-- Reindex lower Levi coordinates by the positions in the list of discrete slots. -/
def entriesBySlot : (CoordM cl → ℝ) ≃ᵐ (Fin (L).length → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (entryEquiv ds).symm

theorem measurePreserving_entriesBySlot :
    MeasurePreserving (entriesBySlot (n := n) ds) volume volume := by
  simpa only [entriesBySlot, ← volume_pi] using
    measurePreserving_piCongrLeft (fun _ => (volume : Measure ℝ)) (entryEquiv ds).symm

theorem entriesBySlot_apply (Z : CoordM cl → ℝ) (i : Fin (L).length) :
    entriesBySlot ds Z i = Z (entryEquiv ds i) := by
  simpa only [entriesBySlot, Equiv.symm_apply_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (entryEquiv ds).symm Z (entryEquiv ds i)

private theorem lowerRootMatrix_mul_of_disjoint {s t : Slot n} (h : s.Disjoint t) :
    lowerRootMatrix n s.p s.hp * lowerRootMatrix n t.p t.hp = 0 := by
  unfold lowerRootMatrix
  refine Matrix.single_mul_single_of_ne _ _ _ _ ?_ _
  intro he
  have hv := Fin.val_eq_of_eq he
  change s.p = t.p + 1 at hv
  rcases h with h | h <;> omega

private theorem lowerBlockProduct_val :
    ∀ (T : List (Slot n)), T.Pairwise Slot.Disjoint → ∀ x : Fin T.length → ℝ,
      (lowerBlockProduct T x).val =
        1 + ∑ i : Fin T.length, x i • lowerRootMatrix n (T.get i).p (T.get i).hp
  | [], _, _ => by simp [lowerBlockProduct]
  | s :: T, h, x => by
      obtain ⟨hs, hT⟩ := List.pairwise_cons.mp h
      let U := ∑ i : Fin T.length, x i.succ • lowerRootMatrix n (T.get i).p (T.get i).hp
      let V := x 0 • lowerRootMatrix n s.p s.hp
      have hUV : U * V = 0 := by
        unfold U V
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [smul_mul_smul_comm, lowerRootMatrix_mul_of_disjoint (hs _ (List.get_mem _ i)).symm,
          smul_zero]
      let A (i : Fin (T.length + 1)) :=
        x i • lowerRootMatrix n ((s :: T).get i).p ((s :: T).get i).hp
      simp only [lowerBlockProduct, Units.val_mul, lowerBlockProduct_val T hT, lowerRootElement_val]
      change (1 + U) * (1 + V) = 1 + ∑ i, A i
      rw [Fin.sum_univ_succ A]
      change (1 + U) * (1 + V) = 1 + (V + U)
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hUV, add_zero]
      abel

private theorem lowerRootMatrix_entryOfSlot (i : Fin (L).length) (p q : Fin n) :
    lowerRootMatrix n ((L).get i).p ((L).get i).hp p q =
      if (entryEquiv ds i).val = (p, q) then 1 else 0 := by
  rw [lowerRootMatrix, Matrix.single_apply]
  congr 1
  change (_ = p ∧ _ = q) = ((_, _) = (p, q))
  rw [Prod.mk.injEq]

/-- The lower Levi matrix is the product of the lower simple-root matrices at
the nonzero-weight slots. -/
def RealDiscreteLeviEntriesStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (Z : CoordM (fun i : Fin n => blockStart ds i) → ℝ),
    lowerMGL (fun i => blockStart ds i) Z =
      lowerBlockProduct (discreteSlots ds n) (entriesBySlot ds Z)

theorem realDiscreteLeviEntries : RealDiscreteLeviEntriesStatement := by
  intro n ds Z
  apply Units.ext
  rw [lowerMGL_val, lowerBlockProduct_val _ (pairwise_discreteSlots ds n)]
  ext p q
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    entriesBySlot_apply, lowerRootMatrix_entryOfSlot, mul_ite, mul_one, mul_zero]
  rw [Equiv.sum_comp (entryEquiv ds) (fun c => if c.val = (p, q) then Z c else 0)]
  by_cases h : blockStart ds p = blockStart ds q ∧ q < p
  · let c : CoordM (fun i : Fin n => blockStart ds i) := ⟨(p, q), h⟩
    have hpq : p ≠ q := h.2.ne'
    have he (z : CoordM (fun i : Fin n => blockStart ds i)) :
        z.val = (p, q) ↔ z = c :=
      ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    simp only [lowerM, Matrix.of_apply, dite_eq_left h, Matrix.one_apply, ite_eq_right hpq, zero_add, he,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  · rw [lowerM, Matrix.of_apply, dite_eq_right h, Matrix.one_apply]
    have hzero : (∑ c : CoordM (fun i : Fin n => blockStart ds i),
        if c.val = (p, q) then Z c else 0) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      apply ite_eq_right
      intro e
      have hc := c.property
      change blockStart ds c.val.1 = blockStart ds c.val.2 ∧ c.val.2 < c.val.1 at hc
      rw [e] at hc
      exact h hc
    rw [hzero, add_zero]

/-- The uniform discrete-block Fourier estimate in the Lebesgue coordinates of
the lower Levi chart. -/
theorem realDiscreteLeviEntryBound
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : ℝ), (∀ g ∈ unitaryCompact ℝ n, ‖f.val g‖ ≤ R) →
        ∀ g ∈ unitaryCompact ℝ n, ∀ s : Fin (L).length → ℝ,
          let J (Z : CoordM cl → ℝ) :=
            f.val (lowerMGL cl Z * g) *
              ∏ i, Complex.exp (↑(-2 * Real.pi * entriesBySlot ds Z i * s i) * Complex.I)
          Integrable J ∧ ‖∫ Z, J Z‖ ≤ C * R * ∏ i, |s i| ^ ((((L).get i).M : ℝ) / 2) := by
  obtain ⟨C, hC, hB⟩ := realDiscreteLeviInnerBound n ds f (L)
    (pairwise_discreteSlots ds n) (fun _ ht => mem_discreteSlots.mp ht)
  refine ⟨C, hC, fun R hR g hg s => ?_⟩
  obtain ⟨hI, hF⟩ := hB R hR g hg s
  let K := lowerBlockKernel (L) f.val g s
  have hK : Integrable K := hI
  have he (Z : CoordM cl → ℝ) :
      f.val (lowerMGL cl Z * g) *
          (∏ i, Complex.exp (↑(-2 * Real.pi * entriesBySlot ds Z i * s i) * Complex.I)) =
        K (entriesBySlot ds Z) := by
    rw [realDiscreteLeviEntries n ds Z]
    rfl
  simp only [he]
  refine ⟨(measurePreserving_entriesBySlot ds).integrable_comp_of_integrable hK, ?_⟩
  rw [(measurePreserving_entriesBySlot ds).integral_comp (entriesBySlot ds).measurableEmbedding K]
  exact hF

end Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviEntries
