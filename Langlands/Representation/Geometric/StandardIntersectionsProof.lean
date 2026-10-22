import Langlands.Representation.Geometric.WeylStatement
import Langlands.Representation.Geometric.MonotoneBlocksProof
import Langlands.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof

namespace Langlands.Geometric

open GeneralLinear

universe u

variable {n : ℕ}

theorem index_blockIndex (B : BlockShape n) (a : Fin n) :
    B.index (blockIndex B a) (B.indexEquiv.symm a).2 = a :=
  B.indexEquiv.apply_symm_apply a

theorem index_ne_of_block_ne (B : BlockShape n) {i j : Fin B.length}
    (h : i ≠ j) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.index i a ≠ B.index j b := by
  intro he
  have := congrArg (blockIndex B) he
  exact h (by simpa only [blockIndex_index] using this)

variable (R : Type u) [CommRing R]

theorem mem_parabolic_iff_blockIndex (B : BlockShape n) (g : GeneralLinear n R) :
    g ∈ B.parabolic R ↔ ∀ a b, blockIndex B b < blockIndex B a → g a b = 0 := by
  rw [B.mem_parabolic_iff]
  constructor
  · intro h a b hab
    simpa only [index_blockIndex] using
      h (blockIndex B a) (blockIndex B b) (B.indexEquiv.symm a).2
        (B.indexEquiv.symm b).2 hab
  · intro h i j a b hij
    exact h _ _ (by simpa only [blockIndex_index] using hij)

theorem mem_unipotent_iff_blockIndex (B : BlockShape n) (g : GeneralLinear n R) :
    g ∈ B.unipotentSubgroup R ↔ g ∈ B.parabolic R ∧
      ∀ a b, blockIndex B a = blockIndex B b →
        g a b = if a = b then 1 else 0 := by
  rw [B.mem_unipotentSubgroup_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h a b hab
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
    change blockIndex B (B.index i a) = blockIndex B (B.index j b) at hab
    simp only [blockIndex_index] at hab
    subst j
    change g (B.index i a) (B.index i b) =
      if B.index i a = B.index i b then 1 else 0
    simpa only [(B.index i).injective.eq_iff] using h i a b
  · intro h i a b
    have he := h (B.index i a) (B.index i b) (by simp only [blockIndex_index])
    simpa only [(B.index i).injective.eq_iff] using he

@[simp] theorem conjugatedLeviMap_entry (B : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) (a b : Fin n) :
    conjugatedLeviMap R B w m (w a) (w b) = B.leviEmbedding R m a b := by
  change (permutation n R w * B.leviEmbedding R m * (permutation n R w)⁻¹)
    (w a) (w b) = _
  rw [permutation_conjugate_entry]
  change B.leviEmbedding R m (w.symm (w a)) (w.symm (w b)) = _
  simp only [Equiv.symm_apply_apply]

theorem conjugatedLeviMap_zero_iff (B : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) (P : Fin n → Fin n → Prop) :
    (∀ a b, P a b → conjugatedLeviMap R B w m a b = 0) ↔
      ∀ i a b, P (w (B.index i a)) (w (B.index i b)) → m i a b = 0 := by
  constructor
  · intro h i a b hab
    simpa only [conjugatedLeviMap_entry, B.leviEmbedding_apply_same] using h _ _ hab
  · intro h a b hab
    obtain ⟨a, rfl⟩ := w.surjective a
    obtain ⟨b, rfl⟩ := w.surjective b
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
    change conjugatedLeviMap R B w m (w (B.index i a)) (w (B.index j b)) = 0
    rw [conjugatedLeviMap_entry]
    by_cases hij : i = j
    · subst j
      rw [B.leviEmbedding_apply_same]
      exact h i a b hab
    · exact B.leviEmbedding_apply_ne R m a b hij

theorem conjugatedLeviMap_identity_iff (B : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) (P : Fin n → Fin n → Prop) :
    (∀ a b, P a b → conjugatedLeviMap R B w m a b = if a = b then 1 else 0) ↔
      ∀ i a b, P (w (B.index i a)) (w (B.index i b)) →
        m i a b = if a = b then 1 else 0 := by
  constructor
  · intro h i a b hab
    simpa only [conjugatedLeviMap_entry, B.leviEmbedding_apply_same,
      w.injective.eq_iff, (B.index i).injective.eq_iff] using h _ _ hab
  · intro h a b hab
    obtain ⟨a, rfl⟩ := w.surjective a
    obtain ⟨b, rfl⟩ := w.surjective b
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
    change conjugatedLeviMap R B w m (w (B.index i a)) (w (B.index j b)) =
      if w (B.index i a) = w (B.index j b) then 1 else 0
    rw [conjugatedLeviMap_entry]
    by_cases hij : i = j
    · subst j
      simpa only [B.leviEmbedding_apply_same, w.injective.eq_iff,
        (B.index i).injective.eq_iff] using h i a b hab
    · rw [B.leviEmbedding_apply_ne R m a b hij]
      simp only [w.injective.eq_iff]
      split_ifs with he
      · exact False.elim (index_ne_of_block_ne B hij a b he)
      · rfl

theorem mem_sourceParabolic_iff (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) : m ∈ sourceParabolic R B C w ↔
      ∀ i a b, blockIndex C (w (B.index i b)) < blockIndex C (w (B.index i a)) →
        m i a b = 0 := by
  change conjugatedLeviMap R B w m ∈ C.parabolic R ↔ _
  rw [mem_parabolic_iff_blockIndex, conjugatedLeviMap_zero_iff]

theorem mem_sourceLevi_iff (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) : m ∈ sourceLevi R B C w ↔
      ∀ i a b, blockIndex C (w (B.index i a)) ≠ blockIndex C (w (B.index i b)) →
        m i a b = 0 := by
  change conjugatedLeviMap R B w m ∈ C.leviSubgroup R ↔ _
  rw [CuspidalSupport.levi_mem_iff, conjugatedLeviMap_zero_iff]

theorem mem_sourceUnipotent_iff (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (m : B.Levi R) : m ∈ sourceUnipotent R B C w ↔
      m ∈ sourceParabolic R B C w ∧
      ∀ i a b, blockIndex C (w (B.index i a)) = blockIndex C (w (B.index i b)) →
        m i a b = if a = b then 1 else 0 := by
  change conjugatedLeviMap R B w m ∈ C.unipotentSubgroup R ↔ _
  rw [mem_unipotent_iff_blockIndex, conjugatedLeviMap_identity_iff]
  rfl

theorem standardIntersections_of_comparisons (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
    (hS : ∀ i a b, blockIndex (S i) a ≤ blockIndex (S i) b ↔
      blockIndex C (w (B.index i a)) ≤ blockIndex C (w (B.index i b))) :
    sourceParabolic R B C w = refinedParabolic R B S ∧
    sourceLevi R B C w = refinedLevi R B S ∧
    sourceUnipotent R B C w = refinedUnipotent R B S := by
  have hlt (i) (a b : Fin (B.size i)) :
      blockIndex (S i) a < blockIndex (S i) b ↔
        blockIndex C (w (B.index i a)) < blockIndex C (w (B.index i b)) := by
    simpa only [← not_le] using not_congr (hS i b a)
  have heq (i) (a b : Fin (B.size i)) :
      blockIndex (S i) a = blockIndex (S i) b ↔
        blockIndex C (w (B.index i a)) = blockIndex C (w (B.index i b)) := by
    simp only [le_antisymm_iff, hS]
  have hp : sourceParabolic R B C w = refinedParabolic R B S := by
    apply Subgroup.ext
    intro m
    simp only [mem_sourceParabolic_iff, refinedParabolic, Subgroup.mem_pi,
      Set.mem_univ, forall_const, mem_parabolic_iff_blockIndex, hlt]
  refine ⟨hp, ?_, ?_⟩
  · apply Subgroup.ext
    intro m
    simp only [mem_sourceLevi_iff, refinedLevi, Subgroup.mem_pi,
      Set.mem_univ, forall_const, CuspidalSupport.levi_mem_iff, ne_eq, heq]
  · apply Subgroup.ext
    intro m
    simp only [mem_sourceUnipotent_iff, hp, refinedParabolic, refinedUnipotent,
      Subgroup.mem_pi, Set.mem_univ, forall_const, mem_unipotent_iff_blockIndex, heq,
      forall_and]

/-- Increasing source-block coordinates give actual standard intersection refinements. -/
theorem exists_standardIntersections
    (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, StrictMono (fun a : Fin (B.size i) => w (B.index i a))) :
    ∃ S : BlockRefinement B,
      sourceParabolic R B C w = refinedParabolic R B S ∧
      sourceLevi R B C w = refinedLevi R B S ∧
      sourceUnipotent R B C w = refinedUnipotent R B S := by
  classical
  have hex (i : Fin B.length) := monotoneBlockShape (B.size i) C.length
    (fun a => blockIndex C (w (B.index i a)))
    ((blockIndex_monotone C).comp (hw i).monotone)
  choose S hS using hex
  exact ⟨S, standardIntersections_of_comparisons R B C w S hS⟩

/-- The exact published two-sided p-adic standard-intersection statement. -/
theorem padicStandardIntersectionsTheorem :
    PadicStandardIntersectionsTheorem.{u} := by
  intro p hp F n hn B C w
  constructor
  · exact exists_standardIntersections F.Carrier B C w.val
      w.property.1
  · exact exists_standardIntersections F.Carrier C B w.val⁻¹
      w.property.2

end Langlands.Geometric
