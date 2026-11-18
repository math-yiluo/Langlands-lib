import Langlands.Correspondence.BushnellKutzkoLabelTowers
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

/-! The positive support and the constant term in the polar-part count. -/

noncomputable section

namespace Langlands.Henniart.LabelCounting

open IntermediateField Langlands.Henniart.Numerical

/-- A descending list of positive levels with initial level `m` and joint gcd `1` with `a`. -/
@[ext] structure PositiveLevels (m a r : ℕ) where
  level : Fin (r + 1) → Fin (m + 1)
  top : level 0 = Fin.last m
  positive : ∀ i, 0 < (level i : ℕ)
  decreasing : StrictAnti level
  gcd_eq : Nat.gcd a (Finset.univ.gcd fun i => (level i : ℕ)) = 1

variable {m a r : ℕ}

private def PositiveLevels.index (l : PositiveLevels m a r) : Fin (r + 2) → Fin (m + 1) :=
  Fin.snoc l.level 0

private theorem PositiveLevels.index_castSucc (l : PositiveLevels m a r) (j : Fin (r + 1)) :
    l.index j.castSucc = l.level j :=
  Fin.snoc_castSucc (α := fun _ => Fin (m + 1)) 0 l.level j

private theorem PositiveLevels.index_last (l : PositiveLevels m a r) :
    l.index (Fin.last (r + 1)) = 0 :=
  Fin.snoc_last (α := fun _ => Fin (m + 1)) 0 l.level

private theorem PositiveLevels.index_injective (l : PositiveLevels m a r) :
    Function.Injective l.index := by
  refine Fin.snoc_injective_of_injective l.decreasing.injective ?_
  rintro ⟨i, hi⟩
  exact (Nat.ne_of_gt (l.positive i)) (congrArg Fin.val hi)

private theorem PositiveLevels.mem_range_index (l : PositiveLevels m a r) (i : Fin (m + 1)) :
    i ∈ Set.range l.index ↔ i = 0 ∨ i ∈ Finset.univ.image l.level := by
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.lastCases with
    | last => exact Or.inl l.index_last
    | cast j => exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (l.index_castSucc j).symm⟩)
  · rintro (rfl | hi)
    · exact ⟨Fin.last _, l.index_last⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.castSucc, l.index_castSucc j⟩

open Classical in
private def positiveSupport {L : Type*} [Zero L] (c : Fin (m + 1) → L) : Finset (Fin (m + 1)) :=
  Finset.univ.filter fun i => 0 < (i : ℕ) ∧ c i ≠ 0

private theorem mem_positiveSupport {L : Type*} [Zero L] (c : Fin (m + 1) → L) (i : Fin (m + 1)) :
    i ∈ positiveSupport c ↔ 0 < (i : ℕ) ∧ c i ≠ 0 := by
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem positiveSupport_gcd {L : Type*} [Field L] (c : Fin (m + 1) → L) :
    polarSupportGcd c = (positiveSupport c).gcd Fin.val := rfl

open Classical in
private def spread {L : Type*} [Zero L] (l : PositiveLevels m a r)
    (x : Fin (r + 2) → L) (i : Fin (m + 1)) : L :=
  if h : i ∈ Set.range l.index then x (Classical.choose h) else 0

private theorem spread_index {L : Type*} [Zero L] (l : PositiveLevels m a r)
    (x : Fin (r + 2) → L) (j : Fin (r + 2)) : spread l x (l.index j) = x j := by
  unfold spread
  rw [dite_eq_left (Set.mem_range_self j)]
  exact congrArg x (l.index_injective (Classical.choose_spec (Set.mem_range_self j)))

private theorem support_spread {L : Type*} [Zero L] (l : PositiveLevels m a r)
    (x : Fin (r + 2) → L) (hx : ∀ j, x j ≠ 0) :
    positiveSupport (spread l x) = Finset.univ.image l.level := by
  have hn (i) : spread l x i ≠ 0 ↔ i ∈ Set.range l.index := by
    by_cases hi : i ∈ Set.range l.index
    · obtain ⟨j, rfl⟩ := hi
      rw [spread_index]
      exact ⟨fun _ => Set.mem_range_self j, fun _ => hx j⟩
    · simp [spread, hi]
  ext i
  rw [mem_positiveSupport, hn, l.mem_range_index]
  constructor
  · rintro ⟨hp, rfl | hi⟩
    · exact (Nat.lt_irrefl 0 hp).elim
    · exact hi
  · intro hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨l.positive j, Or.inr hi⟩

private theorem adjoin_spread {k L : Type*} [Field k] [Field L] [Algebra k L]
    (l : PositiveLevels m a r) (x : Fin (r + 2) → L) :
    adjoin k (Set.range (spread l x)) = adjoin k (Set.range x) := by
  apply le_antisymm <;> rw [adjoin_le_iff]
  · rintro _ ⟨i, rfl⟩
    unfold spread
    split
    · exact subset_adjoin k _ (Set.mem_range_self _)
    · exact zero_mem _
  · rintro _ ⟨j, rfl⟩
    rw [← spread_index l x j]
    exact subset_adjoin k _ (Set.mem_range_self _)

private def descending (s : Finset (Fin (m + 1))) (h : s.card = r + 1)
    (i : Fin (r + 1)) : Fin (m + 1) :=
  s.orderEmbOfFin h i.rev

private theorem descending_image (s : Finset (Fin (m + 1))) (h : s.card = r + 1) :
    Finset.univ.image (descending s h) = s := by
  ext i
  change i ∈ Finset.univ.image (descending s h) ↔ i ∈ (s : Set _)
  rw [← Finset.range_orderEmbOfFin s h, Finset.mem_image, Set.mem_range]
  constructor
  · rintro ⟨j, -, hj⟩
    exact ⟨j.rev, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j.rev, Finset.mem_univ _, by simpa [descending] using hj⟩

private theorem level_eq_descending (l : PositiveLevels m a r)
    {s : Finset (Fin (m + 1))} (h : s.card = r + 1) (hl : ∀ j, l.level j ∈ s) :
    l.level = descending s h := by
  have hsort : (fun j => l.level j.rev) = s.orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h (fun j => hl j.rev)
      (fun _ _ hij => l.decreasing (Fin.rev_lt_rev.mpr hij))
  funext j
  simpa [descending] using congrFun hsort j.rev

private theorem spread_support_card {L : Type*} [Zero L] (l : PositiveLevels m a r)
    (x : Fin (r + 2) → L) (hx : ∀ j, x j ≠ 0) :
    (positiveSupport (spread l x)).card = r + 1 := by
  rw [support_spread l x hx, Finset.card_image_of_injective _ l.decreasing.injective,
    Finset.card_univ, Fintype.card_fin]

/-- Positive support with its nonzero coefficients, followed by the constant coefficient. -/
abbrev SupportedTuples (k L : Type*) [Field k] [Field L] [Algebra k L] (m a : ℕ) :=
  Σ r : ℕ, PositiveLevels m a r × GeneratingTuple k L (r + 2)

section PolarParts

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

private def spreadPolarPart (z : SupportedTuples k L m a) : polarParts k L a m := by
  obtain ⟨r, l, x⟩ := z
  refine ⟨spread l x.val, ?_⟩
  change IsPolarPart k a m (spread l x.val)
  refine ⟨?_, ?_, (adjoin_spread l x.val).trans x.property.2, ?_⟩
  · have h := spread_index l x.val (Fin.last (r + 1))
    rw [l.index_last] at h
    rw [h]
    exact x.property.1 _
  · have h := spread_index l x.val ((0 : Fin (r + 1)).castSucc)
    rw [l.index_castSucc, l.top] at h
    rw [h]
    exact x.property.1 _
  · rw [positiveSupport_gcd, support_spread l x.val x.property.1, Finset.gcd_image]
    exact l.gcd_eq

private theorem spreadPolarPart_injective :
    Function.Injective (spreadPolarPart (k := k) (L := L) (m := m) (a := a)) := by
  rintro ⟨r, l, x⟩ ⟨s, l', x'⟩ h
  have hc : spread l x.val = spread l' x'.val := congrArg Subtype.val h
  have hr : r + 1 = s + 1 := (spread_support_card l x.val x.property.1).symm.trans
    ((congrArg (fun c => (positiveSupport c).card) hc).trans
      (spread_support_card l' x'.val x'.property.1))
  have hrs := Nat.succ.inj hr
  subst s
  have hs : positiveSupport (spread l x.val) = positiveSupport (spread l' x'.val) :=
    congrArg positiveSupport hc
  have hl : l = l' := by
    apply PositiveLevels.ext
    have hcard := spread_support_card l x.val x.property.1
    rw [level_eq_descending l hcard, level_eq_descending l' hcard]
    · intro j
      rw [hs, support_spread l' x'.val x'.property.1]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · intro j
      rw [support_spread l x.val x.property.1]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  subst l'
  have hx : x = x' := Subtype.ext (funext fun j => by
    simpa only [spread_index] using congrFun hc (l.index j))
  subst x'
  rfl

private theorem spreadPolarPart_surjective (hm : 0 < m) :
    Function.Surjective (spreadPolarPart (k := k) (L := L) (m := m) (a := a)) := by
  intro c
  obtain ⟨h0, htop, hgen, hgcd⟩ : IsPolarPart k a m c.val := c.property
  let s := positiveSupport c.val
  have hs : Fin.last m ∈ s := (mem_positiveSupport c.val _).mpr ⟨hm, htop⟩
  obtain ⟨r, hcard⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨_, hs⟩)
  let l : PositiveLevels m a r := {
    level := descending s hcard
    top := by
      change s.orderEmbOfFin hcard (Fin.rev 0) = Fin.last m
      rw [Fin.rev_zero]
      have hmax : s.orderEmbOfFin hcard (Fin.last r) = s.max' ⟨_, hs⟩ :=
        Finset.orderEmbOfFin_last hcard (Nat.succ_pos r)
      rw [hmax]
      exact le_antisymm (Fin.le_last _) (s.le_max' _ hs)
    positive i := ((mem_positiveSupport c.val _).mp
      (s.orderEmbOfFin_mem hcard i.rev)).1
    decreasing := fun _ _ hij => (s.orderEmbOfFin hcard).strictMono (Fin.rev_lt_rev.mpr hij)
    gcd_eq := by
      rw [positiveSupport_gcd] at hgcd
      change Nat.gcd a (s.gcd Fin.val) = 1 at hgcd
      rw [← descending_image s hcard, Finset.gcd_image] at hgcd
      exact hgcd }
  let x : Fin (r + 2) → L := fun j => c.val (l.index j)
  have hx (j : Fin (r + 2)) : x j ≠ 0 := by
    induction j using Fin.lastCases with
    | last =>
      change c.val (l.index (Fin.last (r + 1))) ≠ 0
      simpa only [l.index_last] using h0
    | cast j =>
      change c.val (l.index j.castSucc) ≠ 0
      rw [l.index_castSucc]
      exact ((mem_positiveSupport c.val _).mp (s.orderEmbOfFin_mem hcard j.rev)).2
  have he : spread l x = c.val := by
    funext i
    unfold spread
    split
    · rename_i hi
      exact congrArg c.val (Classical.choose_spec hi)
    · rename_i hi
      have hi' : i ≠ 0 := fun e => hi ((l.mem_range_index _).mpr (Or.inl e))
      have hi'' : 0 < (i : ℕ) := by
        exact Nat.pos_of_ne_zero (fun h => hi' (Fin.ext h))
      refine (not_ne_iff.mp fun hn => hi ?_).symm
      apply (l.mem_range_index _).mpr
      right
      change i ∈ Finset.univ.image (descending s hcard)
      rw [descending_image]
      exact (mem_positiveSupport c.val _).mpr ⟨hi'', hn⟩
  have hxgen : adjoin k (Set.range x) = ⊤ := by
    rw [← adjoin_spread l x, he, hgen]
  exact ⟨⟨r, l, ⟨x, hx, hxgen⟩⟩, Subtype.ext he⟩

/-- On a positive level, a polar part is its ordered support and a generating nonzero tuple. -/
def polarPartsEquiv (hm : 0 < m) : polarParts k L a m ≃ SupportedTuples k L m a :=
  (Equiv.ofBijective spreadPolarPart ⟨spreadPolarPart_injective, spreadPolarPart_surjective hm⟩).symm

/-- At level zero and `a = 1`, the polar parts are generating nonzero one-tuples. -/
def zeroPolarPartsEquiv : polarParts k L 1 0 ≃ GeneratingTuple k L 1 :=
  Equiv.subtypeEquivRight fun c => by
    change IsPolarPart k 1 0 c ↔ (∀ i, c i ≠ 0) ∧ adjoin k (Set.range c) = ⊤
    have h (i : Fin 1) : i = 0 := Subsingleton.elim _ _
    simp only [IsPolarPart, h, Nat.gcd_one_left, and_true, forall_const, ← and_assoc, and_self]

end PolarParts

end Langlands.Henniart.LabelCounting
