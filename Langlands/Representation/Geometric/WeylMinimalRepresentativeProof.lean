import Langlands.Representation.Geometric.WeylStatement
import Langlands.Representation.Geometric.WeylUniquenessProof
import Mathlib.Data.Fin.Tuple.Sort

/-! Existence of minimal block Weyl representatives and the full bijectivity theorem. -/

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

/-- The coordinates of one block are numbered consecutively in increasing order. -/
theorem index_strictMono (B : BlockShape n) (i : Fin B.length) :
    StrictMono (B.index i) := by
  intro a b hab
  change (B.index i a).val < (B.index i b).val
  simp only [BlockShape.index, Function.Embedding.coeFn_mk, BlockShape.indexEquiv,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  have h : (a : ℕ) < b := hab
  omega

/-- The permutation acting by the given permutation inside each individual block. -/
def blockPermOf (B : BlockShape n) (σ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    Equiv.Perm (Fin n) :=
  (B.indexEquiv.symm.trans (Equiv.sigmaCongrRight σ)).trans B.indexEquiv

@[simp] theorem blockPermOf_index (B : BlockShape n)
    (σ : ∀ i, Equiv.Perm (Fin (B.size i))) (i : Fin B.length) (a : Fin (B.size i)) :
    blockPermOf B σ (B.index i a) = B.index i (σ i a) := by
  change B.indexEquiv (Equiv.sigmaCongrRight σ (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩))) =
    B.indexEquiv ⟨i, σ i a⟩
  rw [Equiv.symm_apply_apply]
  rfl

theorem blockPermOf_mem_blockWeyl (B : BlockShape n)
    (σ : ∀ i, Equiv.Perm (Fin (B.size i))) : blockPermOf B σ ∈ blockWeyl B := by
  intro a
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  change blockIndex B (blockPermOf B σ (B.index i x)) = blockIndex B (B.index i x)
  rw [blockPermOf_index, blockIndex_index, blockIndex_index]

/-- A source block Weyl element sorts the target-block labels on every source block. -/
theorem exists_blockWeyl_monotone_labels (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    ∃ b ∈ blockWeyl B, ∀ i,
      Monotone (fun x : Fin (B.size i) => blockIndex C (w (b (B.index i x)))) := by
  refine ⟨blockPermOf B (fun i => Tuple.sort (fun x => blockIndex C (w (B.index i x)))),
    blockPermOf_mem_blockWeyl B _, fun i => ?_⟩
  simp only [blockPermOf_index]
  exact Tuple.monotone_sort (fun x => blockIndex C (w (B.index i x)))

/-- A target block Weyl element sorts the values of a permutation on every target block. -/
theorem exists_blockWeyl_strictMono (C : BlockShape n) (u : Equiv.Perm (Fin n)) :
    ∃ c ∈ blockWeyl C, ∀ j,
      StrictMono (fun y : Fin (C.size j) => u (c (C.index j y))) := by
  refine ⟨blockPermOf C (fun j => Tuple.sort (fun y => u (C.index j y))),
    blockPermOf_mem_blockWeyl C _, fun j => ?_⟩
  simp only [blockPermOf_index]
  exact (Tuple.monotone_sort (fun y => u (C.index j y))).strictMono_of_injective
    ((u.injective.comp (C.index j).injective).comp (Tuple.sort _).injective)

/-- If the inverse increases on every target block, an increase of target-block labels
along an increasing pair forces an increase of values. -/
theorem lt_of_blockIndex_le (C : BlockShape n) {v : Equiv.Perm (Fin n)}
    (hv : ∀ j, StrictMono (fun y : Fin (C.size j) => v.symm (C.index j y)))
    {a a' : Fin n} (haa : a < a') (hL : blockIndex C (v a) ≤ blockIndex C (v a')) :
    v a < v a' := by
  by_contra h
  have h' : v a' ≤ v a := le_of_not_gt h
  have hj : blockIndex C (v a') = blockIndex C (v a) :=
    le_antisymm (blockIndex_monotone C h') hL
  obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq C (a := v a) rfl
  obtain ⟨y', hy'⟩ := exists_index_of_blockIndex_eq C hj
  have hyy : y' ≤ y := by
    rw [← (index_strictMono C (blockIndex C (v a))).le_iff_le, hy, hy']
    exact h'
  have hmono := (hv (blockIndex C (v a))).monotone hyy
  simp only [hy, hy', Equiv.symm_apply_apply] at hmono
  exact (not_le_of_gt haa) hmono

/-- Every permutation lies in the double coset of a minimal representative. -/
theorem exists_minimal_mem_doubleCoset (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    ∃ v : Equiv.Perm (Fin n), IsMinimalRepresentative B C v ∧
      ∃ c ∈ blockWeyl C, ∃ b ∈ blockWeyl B, v = c * w * b := by
  obtain ⟨b, hb, hmono⟩ := exists_blockWeyl_monotone_labels B C w
  obtain ⟨c, hc, hstrict⟩ := exists_blockWeyl_strictMono C (w * b)⁻¹
  have hsymm : ∀ x, (c⁻¹ * w * b).symm x = (w * b)⁻¹ (c x) := by
    intro x
    rw [← Equiv.Perm.inv_def, ← Equiv.Perm.mul_apply,
      show (c⁻¹ * w * b)⁻¹ = (w * b)⁻¹ * c by group]
  have hinv : ∀ j, StrictMono
      (fun y : Fin (C.size j) => (c⁻¹ * w * b).symm (C.index j y)) := by
    intro j
    simpa only [hsymm] using hstrict j
  have hlabel : ∀ a, blockIndex C ((c⁻¹ * w * b) a) = blockIndex C (w (b a)) :=
    fun a => (blockWeyl C).inv_mem hc (w (b a))
  refine ⟨c⁻¹ * w * b, ⟨fun i => ?_, hinv⟩, c⁻¹, (blockWeyl C).inv_mem hc, b, hb, rfl⟩
  intro x x' hxx
  apply lt_of_blockIndex_le C hinv (index_strictMono B i hxx)
  rw [hlabel, hlabel]
  exact hmono i hxx.le

/-- Every Weyl double coset contains a minimal representative. -/
theorem weylDoubleCoset_surjective (B C : BlockShape n) :
    Function.Surjective (weylDoubleCoset B C) := by
  intro q
  obtain ⟨v, hv, c, hc, b, hb, rfl⟩ := exists_minimal_mem_doubleCoset B C q.out
  refine ⟨⟨c * q.out * b, hv⟩, ?_⟩
  calc weylDoubleCoset B C ⟨c * q.out * b, hv⟩ =
        DoubleCoset.mk (blockWeyl C) (blockWeyl B) q.out :=
        DoubleCoset.eq.mpr ⟨c⁻¹, (blockWeyl C).inv_mem hc, b⁻¹, (blockWeyl B).inv_mem hb,
          by group⟩
    _ = q := DoubleCoset.out_eq' q

/-- Minimal representatives parametrize the Weyl double cosets bijectively. -/
theorem weylDoubleCoset_bijective (B C : BlockShape n) :
    Function.Bijective (weylDoubleCoset B C) :=
  ⟨weylDoubleCoset_injective B C, weylDoubleCoset_surjective B C⟩

/-- The published minimal-representative theorem. -/
theorem weylMinimalRepresentativeTheorem : WeylMinimalRepresentativeTheorem :=
  fun _ _ B C => weylDoubleCoset_bijective B C

end Langlands.Geometric
