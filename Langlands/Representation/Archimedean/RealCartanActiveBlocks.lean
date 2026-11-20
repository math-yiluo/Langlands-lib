import Langlands.Representation.Archimedean.RealCartanCompactSupport
import Langlands.Representation.Archimedean.RealBlockRotation

/-! # Block partitions for selected compact rotation factors -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanActiveBlocks

open RealCartanCompactSupport RealCartanFixedFlag

set_option autoImplicit false

local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ
local notation "K" k:max => Matrix.unitaryGroup (Fin k) ℝ
local notation "G" k:max => Langlands.GeneralLinear k ℝ

/-- The starting positions of a set of disjoint adjacent pairs of coordinates. -/
structure ActiveBlocks (n : ℕ) where
  starts : Finset ℕ
  next_lt : ∀ p ∈ starts, p + 1 < n
  disjoint : ∀ p ∈ starts, p + 1 ∉ starts

namespace ActiveBlocks

variable {n : ℕ} (S : ActiveBlocks n)

private def firstPosition (i : Fin n) : ℕ :=
  if 0 < i.val ∧ i.val - 1 ∈ S.starts then i.val - 1 else i.val

private theorem firstPosition_le (i : Fin n) : S.firstPosition i ≤ i.val := by
  unfold firstPosition
  split_ifs <;> omega

private theorem le_firstPosition_add_one (i : Fin n) : i.val ≤ S.firstPosition i + 1 := by
  unfold firstPosition
  split_ifs <;> omega

/-- The position of the first coordinate of each block in the refined layout. -/
abbrev Label := Set.range S.firstPosition

/-- Assign a coordinate to its active pair or singleton block. -/
def label (i : Fin n) : S.Label := ⟨S.firstPosition i, ⟨i, rfl⟩⟩

theorem label_surjective : Function.Surjective S.label := by
  rintro ⟨x, i, rfl⟩
  exact ⟨i, rfl⟩

instance : Finite S.Label := Finite.of_surjective S.label S.label_surjective

theorem label_monotone : Monotone S.label := by
  have h : StrictMono (fun i : Fin n => i.val) := fun _ _ hij => hij
  intro i j hij
  change S.firstPosition i ≤ S.firstPosition j
  rcases lt_or_eq_of_le hij with hlt | rfl
  · have hi := S.firstPosition_le i
    have hj := S.le_firstPosition_add_one j
    have hij' : i.val < j.val := h hlt
    omega
  · rfl

private theorem firstPosition_start (p : ℕ) (hp : p ∈ S.starts) :
    S.firstPosition (⟨p, by have := S.next_lt p hp; omega⟩ : Fin n) = p := by
  have h : ¬(0 < p ∧ p - 1 ∈ S.starts) := by
    rintro ⟨hp₀, hm⟩
    have hdisj := S.disjoint (p - 1) hm
    rw [show p - 1 + 1 = p by omega] at hdisj
    exact hdisj hp
  simp [firstPosition, h]

private theorem firstPosition_next (p : ℕ) (hp : p ∈ S.starts) :
    S.firstPosition (⟨p + 1, S.next_lt p hp⟩ : Fin n) = p := by
  simp [firstPosition, hp]

theorem label_pair (p : ℕ) (hp : p ∈ S.starts) :
    S.label ⟨p, by have := S.next_lt p hp; omega⟩ = S.label ⟨p + 1, S.next_lt p hp⟩ :=
  Subtype.ext ((S.firstPosition_start p hp).trans (S.firstPosition_next p hp).symm)

private theorem fiber_value_le (x : S.Label) (i : BlockFiber S.label x) :
    x.val ≤ i.val.val ∧ i.val.val ≤ x.val + 1 := by
  have hi : S.firstPosition i.val = x.val := congrArg Subtype.val i.2
  exact ⟨hi ▸ S.firstPosition_le i.val, hi ▸ S.le_firstPosition_add_one i.val⟩

theorem card_fiber_le_two (x : S.Label) : Nat.card (BlockFiber S.label x) ≤ 2 := by
  let offset (i : BlockFiber S.label x) : Fin 2 := ⟨i.val.val - x.val, by
    have hi := S.fiber_value_le x i
    omega⟩
  have hinj : Function.Injective offset := by
    intro i j he
    have hi := S.fiber_value_le x i
    have hj := S.fiber_value_le x j
    have hraw : i.val.val - x.val = j.val.val - x.val := congrArg Fin.val he
    exact Subtype.ext (Fin.ext (by omega))
  simpa using Nat.card_le_card_of_injective offset hinj

private theorem card_fiber_start (p : ℕ) (hp : p ∈ S.starts) :
    Nat.card (BlockFiber S.label (S.label ⟨p, by have := S.next_lt p hp; omega⟩)) = 2 := by
  let x := S.label ⟨p, by have := S.next_lt p hp; omega⟩
  apply le_antisymm (S.card_fiber_le_two x)
  let f (j : Fin 2) : BlockFiber S.label x :=
    ⟨⟨p + j.val, by have := S.next_lt p hp; omega⟩, by
      apply Subtype.ext
      change S.firstPosition ⟨p + j.val, _⟩ = S.firstPosition ⟨p, _⟩
      by_cases hj : j.val = 0
      · simp [hj]
      · have hj' : j.val = 1 := by omega
        rw [S.firstPosition_start p hp]
        simpa only [hj'] using S.firstPosition_next p hp⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hn : p + i.val = p + j.val := congrArg (fun i : BlockFiber S.label x => i.val.val) he
    exact Fin.ext (by omega)
  simpa using Nat.card_le_card_of_injective f hinj

private theorem pair_label_in_starts (x : PairBlock S.label) : x.val.val ∈ S.starts := by
  by_contra hx
  have hval (i : BlockFiber S.label x.val) : i.val.val = x.val.val := by
    have he : S.firstPosition i.val = x.val.val := congrArg Subtype.val i.2
    unfold firstPosition at he
    split_ifs at he with hi
    · exact (hx (he ▸ hi.2)).elim
    · exact he
  have hi : Function.Injective (fun _ : BlockFiber S.label x.val => ()) := by
    intro i j _
    exact Subtype.ext (Fin.ext ((hval i).trans (hval j).symm))
  have hcard := Nat.card_le_card_of_injective _ hi
  rw [x.2] at hcard
  simp at hcard

theorem card_pairBlock : Nat.card (PairBlock S.label) = S.starts.card := by
  let f (p : ↥S.starts) : PairBlock S.label :=
    ⟨S.label ⟨p.val, by have := S.next_lt p.val p.2; omega⟩, S.card_fiber_start p.val p.2⟩
  have hf (p : ↥S.starts) : (f p).val.val = p.val := S.firstPosition_start p.val p.2
  have hi : Function.Injective f := fun p q he =>
    Subtype.ext ((hf p).symm.trans ((congrArg (fun x : PairBlock S.label => x.val.val) he).trans
      (hf q)))
  have hs : Function.Surjective f := by
    intro x
    let p : ↥S.starts := ⟨x.val.val, S.pair_label_in_starts x⟩
    exact ⟨p, Subtype.ext (Subtype.ext (hf p))⟩
  simpa using (Nat.card_eq_of_bijective f ⟨hi, hs⟩).symm

/-- Compact matrices diagonal by the refined active blocks. -/
def compactSubgroup : Subgroup (K n) where
  carrier := {k | ∀ i j, S.label i ≠ S.label j → (k : Mat n) i j = 0}
  one_mem' := fun _ _ hij => Matrix.one_apply_ne (fun h => hij (h ▸ rfl))
  mul_mem' := by
    intro g h hg hh i j hij
    change ((g : Mat n) * (h : Mat n)) i j = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hu : S.label i = S.label u
    · rw [hh u j (fun h' => hij (hu.trans h')), mul_zero]
    · rw [hg i u hu, zero_mul]
  inv_mem' := by
    intro g hg i j hij
    have hval : ((g⁻¹ : K n) : Mat n) = (g : Mat n)ᵀ := by
      change star (g : Mat n) = (g : Mat n)ᵀ
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    change (((g⁻¹ : K n) : Mat n) i j) = 0
    rw [hval, Matrix.transpose_apply]
    exact hg j i (Ne.symm hij)

theorem isClosed_compactSubgroup : IsClosed (S.compactSubgroup : Set (K n)) := by
  have h : (S.compactSubgroup : Set (K n)) =
      ⋂ (i : Fin n) (j : Fin n) (_ : S.label i ≠ S.label j),
        {k : K n | (k : Mat n) i j = 0} := by
    ext k
    simp [compactSubgroup]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun _ => isClosed_eq (continuous_subtype_val.matrix_elem i j) continuous_const

theorem signReflection_mem (i : Fin n) : signReflection n i ∈ S.compactSubgroup :=
  fun _ _ hjk => Matrix.diagonal_apply_ne _ (fun h => hjk (h ▸ rfl))

/-- The coordinate rotation as an element of the compact matrix group. -/
def rotation (n p : ℕ) (θ : ℝ) : K n :=
  ⟨(blockRotation n p θ : Mat n), blockRotation_mem_unitaryCompact n p θ⟩

@[simp]
theorem toUnits_rotation (p : ℕ) (θ : ℝ) :
    Unitary.toUnits (rotation n p θ) = blockRotation n p θ :=
  Units.ext rfl

theorem rotation_mem (p : ℕ) (hp : p ∈ S.starts) (θ : ℝ) :
    rotation n p θ ∈ S.compactSubgroup := by
  intro i j hij
  change (blockRotation n p θ : Mat n) i j = 0
  rw [RealBlockRotation.blockRotation_apply (S.next_lt p hp)]
  have h₀ : ∀ u : Fin n, u.val = p → u = ⟨p, by have := S.next_lt p hp; omega⟩ :=
    fun _ h => Fin.ext h
  have h₁ : ∀ u : Fin n, u.val = p + 1 → u = ⟨p + 1, S.next_lt p hp⟩ := fun _ h => Fin.ext h
  split_ifs with h1 h2 h3 h4
  · exact (hij (by rw [h₁ i h1.1, h₀ j h1.2]; exact (S.label_pair p hp).symm)).elim
  · exact (hij (by rw [h₀ i h2.1, h₁ j h2.2]; exact S.label_pair p hp)).elim
  · exact (hij (congrArg S.label h3.1)).elim
  · exact (hij (congrArg S.label h4)).elim
  · rfl

end ActiveBlocks

/-- If the representative Cartan matrix has more nonreal planes than the
selected compact rotation blocks, the corresponding column terms vanish
for tests supported in a suitable neighborhood of the identity. -/
def RealCartanActiveBlocksSupportStatement (α : Type*) : Prop :=
  ∀ (n : ℕ) (S : ActiveBlocks n) (a : Fin n → α) (d : α → ℝ) (g : G n),
    let C := (g : Mat n)
    Function.Surjective a →
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) →
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) →
    C * Cᵀ = diagonal (d ∘ a) → Function.Injective d → C * Cᵀ = Cᵀ * C →
    S.starts.card < Nat.card (PairBlock a) →
    ∃ U : Set (K n), IsOpen U ∧ 1 ∈ U ∧
      ∀ φ : C(K n, ℂ), Function.support φ ⊆ U →
        ∀ (y h : K n), h ∈ S.compactSubgroup → φ (compactArgument g y h) = 0

theorem realCartanActiveBlocksSupport {α : Type*} : RealCartanActiveBlocksSupportStatement α := by
  intro n S a d g C ha hsize hzero hskew hpair hgram hd hnormal hcount
  let p : Set (K n × K n) := Set.univ ×ˢ (S.compactSubgroup : Set (K n))
  have hp : IsCompact p := isCompact_univ.prod S.isClosed_compactSubgroup.isCompact
  have hmiss : ∀ z ∈ p, compactArgument g z.1 z.2 ≠ 1 := by
    intro z hz hfix
    let Q : Mat n := z.1
    have hQ : Q * Qᵀ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.mem_unitaryGroup_iff.mp z.1.2)
    have htri := blockTriangular_conj_of_compactArgument_eq_one S.label_monotone hz.2 hfix
    obtain ⟨π, hπ, _⟩ := exists_perm_of_fixedFlag a S.label d C Q
      hsize hzero hskew hpair hgram hd hnormal (mul_eq_one_comm.mp hQ) hQ htri
    have hle := (pairBlock_le_of_placement ha S.label_surjective S.card_fiber_le_two hπ).1
    rw [S.card_pairBlock] at hle
    exact (not_le_of_gt hcount) hle
  obtain ⟨U, hU, hOne, hvan⟩ := exists_open_neighborhood_of_avoids_one g hp hmiss
  exact ⟨U, hU, hOne, fun φ hφ y h hh => hvan φ hφ (y, h) ⟨Set.mem_univ y, hh⟩⟩

end Langlands.Archimedean.RealCartanActiveBlocks
