import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.Geometric.FlattenedLevi

/-! Minimal conjugating permutations inside the coarse blocks of a product Levi. -/

noncomputable section

namespace Langlands.ProductLeviMinimalIndex

open GeneralLinear Geometric CuspidalSupport

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The flattened block of a coordinate of a coarse block is numbered by that
coarse block and the refinement block of the inner coordinate. -/
theorem blockIndex_flatten_index (i : Fin B.length) (x : Fin (B.size i)) :
    blockIndex (B.flatten S) (B.index i x) =
      B.flattenBlockEquiv S ⟨i, blockIndex (S i) x⟩ := by
  obtain ⟨⟨j, c⟩, rfl⟩ := (S i).indexEquiv.surjective x
  change blockIndex (B.flatten S) (B.index i ((S i).index j c)) =
    B.flattenBlockEquiv S ⟨i, blockIndex (S i) ((S i).index j c)⟩
  rw [blockIndex_index, B.index_index_eq_flatten S ⟨i, j⟩ c, blockIndex_index]

/-- The coarse block of a coordinate is the outer label of its flattened block. -/
theorem blockIndex_eq_flatten (a : Fin n) :
    blockIndex B a = ((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S) a)).1 := by
  obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
  rw [blockIndex_flatten_index, Equiv.symm_apply_apply, blockIndex_index]

/-- Two coordinates of one coarse block lie in a common flattened block exactly
when they lie in a common block of its refinement. -/
theorem blockIndex_flatten_index_eq_iff (i : Fin B.length) (x y : Fin (B.size i)) :
    blockIndex (B.flatten S) (B.index i x) = blockIndex (B.flatten S) (B.index i y) ↔
      blockIndex (S i) x = blockIndex (S i) y := by
  rw [blockIndex_flatten_index, blockIndex_flatten_index,
    (B.flattenBlockEquiv S).injective.eq_iff, Sigma.mk.inj_iff]
  simp

/-- Coordinates of different coarse blocks lie in different flattened blocks. -/
theorem blockIndex_flatten_index_ne {i i' : Fin B.length} (h : i ≠ i')
    (x : Fin (B.size i)) (y : Fin (B.size i')) :
    blockIndex (B.flatten S) (B.index i x) ≠ blockIndex (B.flatten S) (B.index i' y) := by
  intro e
  apply h
  have := congrArg (fun k => ((B.flattenBlockEquiv S).symm k).1) e
  simpa only [← blockIndex_eq_flatten, blockIndex_index] using this

/-- The fine block Weyl group lies in the coarse one. -/
theorem blockWeyl_flatten_le : blockWeyl (B.flatten S) ≤ blockWeyl B := by
  intro w hw a
  rw [blockIndex_eq_flatten B S (w a), blockIndex_eq_flatten B S a, hw a]

/-- A pair condition on coordinates sharing a flattened block is the same as the
corresponding condition inside every coarse block and its refinement. -/
theorem forall_flatten_pairs_iff {P : Fin n → Fin n → Prop} :
    (∀ a b, blockIndex (B.flatten S) a = blockIndex (B.flatten S) b → P a b) ↔
      ∀ i (x y : Fin (B.size i)), blockIndex (S i) x = blockIndex (S i) y →
        P (B.index i x) (B.index i y) := by
  constructor
  · intro h i x y hxy
    exact h _ _ ((blockIndex_flatten_index_eq_iff B S i x y).mpr hxy)
  · intro h a b hab
    obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
    obtain ⟨i', y, rfl⟩ := TotalConjugatingCount.index_surjective B b
    by_cases hi : i = i'
    · subst i'
      exact h i x y ((blockIndex_flatten_index_eq_iff B S i x y).mp hab)
    · exact absurd hab (blockIndex_flatten_index_ne B S hi x y)

/-- The inverse of a block-diagonal permutation acts by the inverse permutations. -/
theorem blockPermOf_symm_index (σ : ∀ i, Equiv.Perm (Fin (B.size i)))
    (i : Fin B.length) (x : Fin (B.size i)) :
    (blockPermOf B σ).symm (B.index i x) = B.index i ((σ i).symm x) := by
  apply (blockPermOf B σ).injective
  rw [Equiv.apply_symm_apply, blockPermOf_index, Equiv.apply_symm_apply]

/-- The inverse of a block-diagonal permutation is block diagonal. -/
theorem blockPermOf_symm (σ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    (blockPermOf B σ).symm = blockPermOf B (fun i => (σ i).symm) := by
  ext a
  obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
  rw [blockPermOf_symm_index, blockPermOf_index]

/-- Block-diagonal permutations determine their blocks. -/
theorem blockPermOf_injective :
    Function.Injective (blockPermOf B) := by
  intro σ τ h
  funext i
  ext x
  have := congrArg (fun w : Equiv.Perm (Fin n) => w (B.index i x)) h
  simp only [blockPermOf_index] at this
  exact congrArg Fin.val ((B.index i).injective this)

/-- Every coarse block Weyl element is block diagonal. -/
theorem exists_blockPermOf {w : Equiv.Perm (Fin n)} (hw : w ∈ blockWeyl B) :
    ∃ σ : ∀ i, Equiv.Perm (Fin (B.size i)), blockPermOf B σ = w := by
  have hex : ∀ i (x : Fin (B.size i)), ∃ y : Fin (B.size i), B.index i y = w (B.index i x) :=
    fun i x => exists_index_of_blockIndex_eq B ((hw (B.index i x)).trans (blockIndex_index B i x))
  choose f hf using hex
  have hinj : ∀ i, Function.Injective (f i) := by
    intro i x y hxy
    apply (B.index i).injective
    apply w.injective
    rw [← hf, ← hf, hxy]
  refine ⟨fun i => Equiv.ofBijective (f i) (Finite.injective_iff_bijective.mp (hinj i)), ?_⟩
  ext a
  obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
  rw [blockPermOf_index, Equiv.ofBijective_apply, hf]

/-- A block-diagonal permutation is a minimal representative for the flattened
shape exactly when each block is minimal for its refinement. -/
theorem isMinimalRepresentative_blockPermOf_iff (σ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    IsMinimalRepresentative (B.flatten S) (B.flatten S) (blockPermOf B σ) ↔
      ∀ i, IsMinimalRepresentative (S i) (S i) (σ i) := by
  simp only [isMinimalRepresentative_iff]
  have h1 := forall_flatten_pairs_iff B S
    (P := fun a b => a < b → blockPermOf B σ a < blockPermOf B σ b)
  have h2 := forall_flatten_pairs_iff B S
    (P := fun a b => a < b → (blockPermOf B σ).symm a < (blockPermOf B σ).symm b)
  simp only [blockPermOf_index, blockPermOf_symm_index,
    (index_strictMono B _).lt_iff_lt] at h1 h2
  rw [h1, h2]
  constructor
  · rintro ⟨ha, hb⟩ i
    exact ⟨ha i, hb i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

variable {F : Type*} [Field F]

/-- A block-diagonal permutation conjugates the flattened Levi to itself exactly
when each block conjugates the Levi of its refinement to itself. -/
theorem conjugatesLevi_blockPermOf_iff (σ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    ConjugatesLevi (F := F) (B.flatten S) (B.flatten S) (blockPermOf B σ) ↔
      ∀ i, ConjugatesLevi (F := F) (S i) (S i) (σ i) := by
  simp only [TotalConjugatingCount.conjugatesLevi_iff]
  constructor
  · intro h i x y
    have := h (B.index i x) (B.index i y)
    rwa [blockPermOf_index, blockPermOf_index, blockIndex_flatten_index_eq_iff,
      blockIndex_flatten_index_eq_iff] at this
  · intro h a b
    obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
    obtain ⟨i', y, rfl⟩ := TotalConjugatingCount.index_surjective B b
    rw [blockPermOf_index, blockPermOf_index]
    by_cases hi : i = i'
    · subst i'
      rw [blockIndex_flatten_index_eq_iff, blockIndex_flatten_index_eq_iff]
      exact h i x y
    · exact iff_of_false (blockIndex_flatten_index_ne B S hi x y)
        (blockIndex_flatten_index_ne B S hi _ _)

/-- Minimal flattened self-conjugating permutations inside the coarse block
Weyl group, the index type of the product-Levi statement. -/
abbrev CoarseMinimalPermutations :=
  {w : MinimalConjugatingPermutations (F := F) (B.flatten S) (B.flatten S) //
    w.val.val ∈ blockWeyl B}

/-- Assemble one minimal self-conjugating permutation in every coarse block. -/
def assemble (v : ∀ i, MinimalConjugatingPermutations (F := F) (S i) (S i)) :
    CoarseMinimalPermutations (F := F) B S :=
  ⟨⟨⟨blockPermOf B (fun i => (v i).val.val),
      (isMinimalRepresentative_blockPermOf_iff B S _).mpr fun i => (v i).val.property⟩,
      (conjugatesLevi_blockPermOf_iff B S _).mpr fun i => (v i).property⟩,
    blockPermOf_mem_blockWeyl B _⟩

@[simp] theorem assemble_val (v : ∀ i, MinimalConjugatingPermutations (F := F) (S i) (S i)) :
    (assemble B S v).val.val.val = blockPermOf B (fun i => (v i).val.val) := rfl

theorem assemble_bijective :
    Function.Bijective (assemble (F := F) B S) := by
  constructor
  · intro v v' h
    have h' := blockPermOf_injective B (congrArg (fun w => w.val.val.val) h)
    funext i
    exact Subtype.ext (Subtype.ext (congrFun h' i))
  · rintro ⟨⟨⟨w, hmin⟩, hconj⟩, hw⟩
    obtain ⟨σ, rfl⟩ := exists_blockPermOf B hw
    have hmin' := (isMinimalRepresentative_blockPermOf_iff B S σ).mp hmin
    have hconj' := (conjugatesLevi_blockPermOf_iff (F := F) B S σ).mp hconj
    exact ⟨fun i => ⟨⟨σ i, hmin' i⟩, hconj' i⟩, rfl⟩

/-- The product of the block index types is the restricted flattened index type. -/
def assembleEquiv :
    (∀ i, MinimalConjugatingPermutations (F := F) (S i) (S i)) ≃
      CoarseMinimalPermutations (F := F) B S :=
  Equiv.ofBijective _ (assemble_bijective B S)

@[simp] theorem assembleEquiv_apply
    (v : ∀ i, MinimalConjugatingPermutations (F := F) (S i) (S i)) :
    assembleEquiv B S v = assemble B S v := rfl

section Transport

variable (F : Type*) [Field F]

/-- Conjugating every diagonal block by its own permutation matrix is
conjugation of the embedded block-diagonal matrix by the assembled permutation. -/
theorem leviEmbedding_conj_blockPermOf (σ : ∀ i, Equiv.Perm (Fin (B.size i)))
    (X : B.Levi F) :
    B.leviEmbedding F (fun i => permutation (B.size i) F (σ i) * X i *
        (permutation (B.size i) F (σ i))⁻¹) =
      permutation n F (blockPermOf B σ) * B.leviEmbedding F X *
        (permutation n F (blockPermOf B σ))⁻¹ := by
  apply Units.ext
  ext a b
  obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective B a
  obtain ⟨j, y, rfl⟩ := TotalConjugatingCount.index_surjective B b
  rw [permutation_conjugate_entry, Equiv.Perm.inv_def, blockPermOf_symm_index,
    blockPermOf_symm_index]
  by_cases hij : i = j
  · subst hij
    rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same, permutation_conjugate_entry,
      Equiv.Perm.inv_def]
  · rw [B.leviEmbedding_apply_ne F _ _ _ hij, B.leviEmbedding_apply_ne F _ _ _ hij]

/-- Nested block-diagonal inclusion of a family of inner Levi elements. -/
private theorem nestedEmbedding_injective :
    Function.Injective (fun X : ∀ i, (S i).Levi F =>
      B.leviEmbedding F (refinedLeviEquiv F B S X).val) :=
  fun _ _ h => (refinedLeviEquiv F B S).injective
    (Subtype.ext (B.leviEmbedding_injective F h))

/-- Under the flattened product coordinates, conjugation of the flattened Levi by an
assembled block-diagonal permutation is blockwise conjugation by its blocks. -/
theorem flattenedLeviProductEquiv_leviConjugation (σ : ∀ i, Equiv.Perm (Fin (B.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := F) (S i) (S i) (σ i))
    (hw : ConjugatesLevi (F := F) (B.flatten S) (B.flatten S) (blockPermOf B σ))
    (m : (B.flatten S).Levi F) :
    flattenedLeviProductEquiv F B S
        (leviConjugation (B.flatten S) (B.flatten S) (blockPermOf B σ) hw m) =
      fun i => leviConjugation (S i) (S i) (σ i) (hσ i) (flattenedLeviProductEquiv F B S m i) := by
  apply nestedEmbedding_injective B S F
  have hflat : ∀ y : (B.flatten S).Levi F,
      B.leviEmbedding F (refinedLeviEquiv F B S (flattenedLeviProductEquiv F B S y)).val =
        (B.flatten S).leviEmbedding F y := flattenedLeviEquiv_embedding F B S
  simp only
  rw [hflat, leviConjugation_embedding, ← hflat]
  change _ = B.leviEmbedding F (fun i => (S i).leviEmbedding F
    (leviConjugation (S i) (S i) (σ i) (hσ i) (flattenedLeviProductEquiv F B S m i)))
  simp only [leviConjugation_embedding]
  rw [leviEmbedding_conj_blockPermOf]
  rfl

/-- The inverse conjugations, used by `CuspidalSupport.transport`, are also blockwise. -/
theorem flattenedLeviProductEquiv_leviConjugation_symm
    (σ : ∀ i, Equiv.Perm (Fin (B.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := F) (S i) (S i) (σ i))
    (hw : ConjugatesLevi (F := F) (B.flatten S) (B.flatten S) (blockPermOf B σ))
    (m : (B.flatten S).Levi F) :
    flattenedLeviProductEquiv F B S
        ((leviConjugation (B.flatten S) (B.flatten S) (blockPermOf B σ) hw).symm m) =
      fun i => (leviConjugation (S i) (S i) (σ i) (hσ i)).symm
        (flattenedLeviProductEquiv F B S m i) := by
  set m' := (leviConjugation (B.flatten S) (B.flatten S) (blockPermOf B σ) hw).symm m
  have hm : m = leviConjugation (B.flatten S) (B.flatten S) (blockPermOf B σ) hw m' := by
    rw [MulEquiv.apply_symm_apply]
  rw [hm, flattenedLeviProductEquiv_leviConjugation B S F σ hσ hw]
  funext i
  rw [MulEquiv.symm_apply_apply]

end Transport

end Langlands.ProductLeviMinimalIndex
