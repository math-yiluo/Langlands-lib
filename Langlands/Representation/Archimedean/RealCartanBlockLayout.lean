import Langlands.Representation.Archimedean.RealStandardEllipticCartanBelowTop
import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.RealBlockPositionData

/-! # The original real blocks as a Levi coordinate partition -/

noncomputable section

open Matrix Function

namespace Langlands.Archimedean.RealCartanBlockLayout

open Langlands.LocalFactor.Archimedean GramFormula RealLeviChart RealInducedBlockBound
  RealInducedStandardBound RealCartanCompactSupport RealStandardEllipticCartan
  RealBlockPosition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ}

/-- The sizes of the original list blocks in their given order. -/
abbrev blockSizes (b : Fin c → RealBlock) : Fin c → ℕ := fun i => (b i).rank

local notation "N" b:max => ∑ i, blockSizes b i

@[simp]
theorem realRank_singleton (b : RealBlock) : realRank [b] = b.rank := by
  rw [realRank_cons, realRank_nil, add_zero]

private theorem flat_singletons : ∀ {c : ℕ} (b : Fin c → RealBlock),
    RealLeviSlices.flat (fun i => [b i]) = List.ofFn b
  | 0, _ => rfl
  | c + 1, b => by rw [RealLeviSlices.flat_succ, List.ofFn_succ, flat_singletons]; rfl

theorem realRank_ofFn (b : Fin c → RealBlock) : realRank (List.ofFn b) = N b := by
  rw [← flat_singletons b, RealLeviSlices.realRank_flat]
  simp [RealLeviSlices.sz]

private theorem sz_singletons (b : Fin c → RealBlock) : RealLeviSlices.sz (fun i => [b i]) = blockSizes b :=
  funext fun i => realRank_singleton (b i)

theorem blockSizes_pos (b : Fin c → RealBlock) (i : Fin c) : 0 < blockSizes b i := by
  change 0 < (b i).rank
  cases b i <;> simp [RealBlock.rank]

theorem blockSizes_le_two (b : Fin c → RealBlock) (i : Fin c) : blockSizes b i ≤ 2 := by
  change (b i).rank ≤ 2
  cases b i <;> simp [RealBlock.rank]

/-- The positions in a block are exactly its label fiber. -/
def posFiberEquiv (sz : Fin c → ℕ) (i : Fin c) : Fin (sz i) ≃ BlockFiber (cls sz) i :=
  Equiv.ofBijective (fun a => ⟨pos sz i a, cls_pos sz i a⟩) (by
    constructor
    · intro a b h
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (finSigmaFinEquiv.injective (congrArg Subtype.val h))).2
    · rintro ⟨p, hp⟩
      have he := pos_cls sz p
      rw [hp] at he
      obtain ⟨a, ha⟩ := he
      exact ⟨a, Subtype.ext ha⟩)

@[simp]
theorem card_cls_fiber (sz : Fin c → ℕ) (i : Fin c) : Nat.card (BlockFiber (cls sz) i) = sz i := by
  rw [← Nat.card_congr (posFiberEquiv sz i), Nat.card_fin]

theorem cls_surjective (b : Fin c → RealBlock) : Surjective (cls (blockSizes b)) := fun i =>
  ⟨pos (blockSizes b) i ⟨0, blockSizes_pos b i⟩, cls_pos _ _ _⟩

theorem card_cls_fiber_le_two (b : Fin c → RealBlock) (i : Fin c) :
    Nat.card (BlockFiber (cls (blockSizes b)) i) ≤ 2 := by
  simpa only [card_cls_fiber] using blockSizes_le_two b i

theorem character_pos (b : Fin c → RealBlock) (i : Fin c) (a : Fin (blockSizes b i)) :
    realPositionCharacter (List.ofFn b) (pos (blockSizes b) i a) = realPositionCharacter [b i] a := by
  have h := RealLeviSlices.realPositionCharacter_flat (fun j => [b j]) i a
    (by rw [sz_singletons]; exact a.2)
  rw [flat_singletons, sz_singletons] at h
  rw [val_pos]
  exact h

theorem induced_pos (b : Fin c → RealBlock) (i : Fin c) (a : Fin (blockSizes b i)) :
    realInducedBlockAt (List.ofFn b) (pos (blockSizes b) i a) = realInducedBlockAt [b i] a := by
  have h := RealLeviSlices.realInducedBlockAt_flat (fun j => [b j]) i a
    (by rw [sz_singletons]; exact a.2)
  rw [flat_singletons, sz_singletons] at h
  rw [val_pos]
  exact h

private theorem exponent_flat : ∀ {c : ℕ} (b : Fin c → List RealBlock) (i : Fin c)
    (a : ℕ), a < RealLeviSlices.sz b i →
    realPositionExponent (RealLeviSlices.flat b) (start (RealLeviSlices.sz b) i + a) =
      realPositionExponent (b i) a
  | 0, _, i, _, _ => i.elim0
  | c + 1, b, i, a, ha => by
    rw [RealLeviSlices.flat_succ]
    induction i using Fin.cases with
    | zero =>
      change a < realRank (b 0) at ha
      rw [Fin.val_zero, RealLeviSlices.start_zero', zero_add, realPositionExponent_append,
        ite_eq_left ha]
    | succ i =>
      rw [Fin.val_succ, RealLeviSlices.start_succ', add_assoc]
      have he : RealLeviSlices.sz b 0 = realRank (b 0) := rfl
      rw [he, realPositionExponent_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      exact exponent_flat (fun j => b j.succ) i a ha

theorem exponent_pos (b : Fin c → RealBlock) (i : Fin c) (a : Fin (blockSizes b i)) :
    realPositionExponent (List.ofFn b) (pos (blockSizes b) i a) = realPositionExponent [b i] a := by
  have h := exponent_flat (fun j => [b j]) i a (by rw [sz_singletons]; exact a.2)
  rw [flat_singletons, sz_singletons] at h
  rw [val_pos]
  exact h

private theorem count_induced_ofFn (b : Fin c → RealBlock) :
    (List.ofFn b).countP isInducedBlock = ∑ i, if isInducedBlock (b i) then 1 else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.countP_cons, ih]
    split_ifs <;> simp [add_comm]

theorem card_pairBlock_eq_slots (b : Fin c → RealBlock) :
    Nat.card (PairBlock (cls (blockSizes b))) = (slots (List.ofFn b) (N b)).length := by
  have hC (i : Fin c) : Nat.card (BlockFiber (cls (blockSizes b)) i) = 2 ↔ isInducedBlock (b i) = true := by
    rw [card_cls_fiber]
    change (b i).rank = 2 ↔ isInducedBlock (b i) = true
    cases b i <;> simp [RealBlock.rank, isInducedBlock]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hC), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, length_slots_eq_count_induced (realRank_ofFn b), count_induced_ofFn]

private theorem slotAt_position (b : Fin c → RealBlock) (i : Fin c) (a : Fin (blockSizes b i))
    {s : Slot (N b)} (hs : s ∈ slotAt (List.ofFn b) (N b) (pos (blockSizes b) i a)) :
    (a : ℕ) = 0 := by
  obtain ⟨d, _, hd, _⟩ := mem_slotAt hs
  rw [induced_pos] at hd
  cases hb : b i with
  | character r =>
    have ha := a.2
    change (a : ℕ) < (b i).rank at ha
    have hsize : (b i).rank = 1 := by simp [hb, RealBlock.rank]
    omega
  | induced t =>
    have ha := a.2
    change (a : ℕ) < (b i).rank at ha
    have hsize : (b i).rank = 2 := by simp [hb, RealBlock.rank]
    by_contra hne
    have he : (a : ℕ) = 1 := by omega
    simp [hb, he, realInducedBlockAt] at hd

/-- The slot associated with the start of a block in the given list. -/
def blockSlot (b : Fin c → RealBlock) (i : Fin c) : Option (Slot (N b)) :=
  slotAt (List.ofFn b) (N b) (start (blockSizes b) i)

theorem slotAt_start_induced (b : Fin c → RealBlock) (i : Fin c) (d : ComplexCharacterData)
    (h : b i = .induced d) : realInducedBlockAt (List.ofFn b) (start (blockSizes b) i) = some d := by
  let a : Fin (blockSizes b i) := ⟨0, blockSizes_pos b i⟩
  have he := induced_pos b i a
  rw [show (pos (blockSizes b) i a : ℕ) = start (blockSizes b) i by rw [val_pos]; exact Nat.add_zero _] at he
  rw [he, h]
  rfl

theorem blockSlot_character (b : Fin c → RealBlock) (i : Fin c) (d : RealCharacterData)
    (h : b i = .character d) : blockSlot b i = none := by
  let a : Fin (blockSizes b i) := ⟨0, blockSizes_pos b i⟩
  have he := induced_pos b i a
  rw [show (pos (blockSizes b) i a : ℕ) = start (blockSizes b) i by rw [val_pos]; exact Nat.add_zero _] at he
  rw [blockSlot, slotAt, he, h]
  rfl

theorem blockSlot_induced (b : Fin c → RealBlock) (i : Fin c) (d : ComplexCharacterData)
    (h : b i = .induced d) : ∃ hp : start (blockSizes b) i + 1 < N b,
      blockSlot b i = some (mkSlot (List.ofFn b) (N b) (start (blockSizes b) i) hp d) := by
  have he := slotAt_start_induced b i d h
  have hp := (realRank_ofFn b) ▸ realInducedBlockAt_lt he
  exact ⟨hp, by simp only [blockSlot, slotAt, he, hp, ↓reduceDIte]⟩

private theorem start_injective (b : Fin c → RealBlock) :
    Injective (fun i : Fin c => start (blockSizes b) i) := by
  apply StrictMono.injective
  intro i j h
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (blockSizes_pos b i))
    (start_succ_le (blockSizes b) h i.2)

/-- The list of existing Fourier slots is the list of induced-block slots from the same layout. -/
theorem slots_perm_blockSlots (b : Fin c → RealBlock) :
    (slots (List.ofFn b) (N b)).Perm ((List.finRange c).filterMap (blockSlot b)) := by
  have hleft : (slots (List.ofFn b) (N b)).Nodup :=
    (pairwise_slots _ _).imp fun {s t} ht => fun he => by
      subst t
      unfold Slot.Disjoint at ht
      omega
  have hright : ((List.finRange c).filterMap (blockSlot b)).Nodup :=
    (List.nodup_finRange c).filterMap fun i j s hi hj => by
      obtain ⟨_, _, _, hs⟩ := mem_slotAt hi
      obtain ⟨_, _, _, ht⟩ := mem_slotAt hj
      exact start_injective b (congrArg Slot.p (hs.symm.trans ht))
  apply (List.perm_ext_iff_of_nodup hleft hright).mpr
  intro s
  constructor
  · intro hs
    obtain ⟨p, hp, hslot⟩ := List.mem_filterMap.mp hs
    have hp' : p < N b := List.mem_range.mp hp
    let q : Fin (N b) := ⟨p, hp'⟩
    obtain ⟨a, hq⟩ := pos_cls (blockSizes b) q
    have hsp : s ∈ slotAt (List.ofFn b) (N b) (pos (blockSizes b) (cls (blockSizes b) q) a) := by
      rw [hq]
      exact Option.mem_def.mpr hslot
    have ha := slotAt_position b (cls (blockSizes b) q) a hsp
    have hstart : p = start (blockSizes b) (cls (blockSizes b) q) := calc
      _ = (pos (blockSizes b) (cls (blockSizes b) q) a : ℕ) := congrArg Fin.val hq.symm
      _ = _ := by rw [val_pos, ha, add_zero]
    exact List.mem_filterMap.mpr ⟨cls (blockSizes b) q, List.mem_finRange _,
      by simpa only [blockSlot, ← hstart] using hslot⟩
  · intro hs
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hs
    obtain ⟨_, hp, _, _⟩ := mem_slotAt (Option.mem_def.mpr hi)
    exact List.mem_filterMap.mpr ⟨start (blockSizes b) i, List.mem_range.mpr (by omega), hi⟩

/-- All coordinate signs of the original list can be grouped into its blocks. -/
theorem positions_perm_blockPositions (sz : Fin c → ℕ) :
    (List.ofFn id : List (Fin (∑ i, sz i))).Perm
      ((List.finRange c).flatMap fun i => List.ofFn (pos sz i)) := by
  have hn : ((List.finRange c).flatMap fun i => List.ofFn (pos sz i)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => List.nodup_ofFn.mpr ?_, (List.nodup_finRange c).imp ?_⟩
    · intro a b h
      exact eq_of_heq (Sigma.mk.inj_iff.mp (finSigmaFinEquiv.injective h)).2
    · intro i j hij
      apply List.disjoint_left.mpr
      intro p hi hj
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hi
      obtain ⟨b, hb⟩ := List.mem_ofFn.mp hj
      exact hij (by simpa only [cls_pos] using congrArg (cls sz) hb.symm)
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr injective_id) hn).mpr
  intro p
  constructor
  · intro _
    obtain ⟨a, ha⟩ := pos_cls sz p
    exact List.mem_flatMap.mpr ⟨cls sz p, List.mem_finRange _, List.mem_ofFn.mpr ⟨a, ha⟩⟩
  · intro _
    exact List.mem_ofFn.mpr ⟨p, rfl⟩

/-- The original real list has the required ordered block coordinates, with
one rotation slot at the first position of each induced block. -/
def RealCartanBlockLayoutStatement : Prop :=
  ∀ (c : ℕ) (b : Fin c → RealBlock),
    realRank (List.ofFn b) = N b ∧
    Nat.card (PairBlock (cls (blockSizes b))) = (slots (List.ofFn b) (N b)).length ∧
    (slots (List.ofFn b) (N b)).Perm ((List.finRange c).filterMap (blockSlot b))

theorem realCartanBlockLayout : RealCartanBlockLayoutStatement := fun _ b =>
  ⟨realRank_ofFn b, card_pairBlock_eq_slots b, slots_perm_blockSlots b⟩

end Langlands.Archimedean.RealCartanBlockLayout
