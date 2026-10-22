import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof

/-! Reordering the blocks of a standard block shape, and the block maps of
minimal Levi-conjugating permutations. -/

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n)

/-- Reorder the blocks: block `i` of the new shape is block `e i` of `B`. -/
def permute (e : Equiv.Perm (Fin B.length)) : BlockShape n where
  length := B.length
  size i := B.size (e i)
  positive i := B.positive (e i)
  sum_eq := (Equiv.sum_comp e B.size).trans B.sum_eq

@[simp] theorem permute_length (e : Equiv.Perm (Fin B.length)) :
    (B.permute e).length = B.length := rfl

@[simp] theorem permute_size (e : Equiv.Perm (Fin B.length)) (i : Fin B.length) :
    (B.permute e).size i = B.size (e i) := rfl

/-- Block coordinates of the permuted shape, relabelled as coordinates of `B`. -/
def permuteIndexEquiv (e : Equiv.Perm (Fin B.length)) : (B.permute e).Index ≃ B.Index :=
  Equiv.sigmaCongrLeft (β := fun i : Fin B.length => Fin (B.size i)) e

/-- The coordinate permutation moving block `e i` of `B` onto block `i` of the
permuted shape, keeping the position inside the block. -/
def blockPermutation (e : Equiv.Perm (Fin B.length)) : Equiv.Perm (Fin n) :=
  B.indexEquiv.symm.trans ((B.permuteIndexEquiv e).symm.trans (B.permute e).indexEquiv)

@[simp] theorem blockPermutation_index (e : Equiv.Perm (Fin B.length)) (i : Fin B.length)
    (x : Fin (B.size (e i))) :
    B.blockPermutation e (B.index (e i) x) = (B.permute e).index i x := by
  change (B.permute e).indexEquiv ((B.permuteIndexEquiv e).symm
    (B.indexEquiv.symm (B.indexEquiv ⟨e i, x⟩))) = (B.permute e).indexEquiv ⟨i, x⟩
  rw [Equiv.symm_apply_apply]
  congr 1
  rw [Equiv.symm_apply_eq]
  rfl

@[simp] theorem blockPermutation_symm_index (e : Equiv.Perm (Fin B.length))
    (i : Fin B.length) (x : Fin (B.size (e i))) :
    (B.blockPermutation e).symm ((B.permute e).index i x) = B.index (e i) x := by
  rw [Equiv.symm_apply_eq, blockPermutation_index]

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe u

variable {n : ℕ}

theorem blockIndex_blockPermutation (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
    (a : Fin n) :
    blockIndex (B.permute e) (B.blockPermutation e a) = e.symm (blockIndex B a) := by
  obtain ⟨⟨k, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨i, rfl⟩ := e.surjective k
  change blockIndex (B.permute e) (B.blockPermutation e (B.index (e i) x)) =
    e.symm (blockIndex B (B.index (e i) x))
  rw [BlockShape.blockPermutation_index, blockIndex_index]
  exact (blockIndex_index (B.permute e) i x).trans (e.symm_apply_apply i).symm

/-- Order preservation inside every block, restated on coordinates. -/
theorem strictMono_index_iff (B : BlockShape n) (w : Fin n → Fin n) :
    (∀ i, StrictMono (fun x : Fin (B.size i) => w (B.index i x))) ↔
      ∀ a b, blockIndex B a = blockIndex B b → a < b → w a < w b := by
  constructor
  · intro h a b hab hlt
    obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B (a := a) rfl
    obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq B (a := b) hab.symm
    rw [← hx, ← hy] at hlt ⊢
    exact h _ ((index_strictMono B _).lt_iff_lt.mp hlt)
  · intro h i x y hxy
    exact h _ _ (by rw [blockIndex_index, blockIndex_index]) (index_strictMono B i hxy)

/-- The minimality condition, restated on coordinates. -/
theorem isMinimalRepresentative_iff (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    IsMinimalRepresentative B C w ↔
      (∀ a b, blockIndex B a = blockIndex B b → a < b → w a < w b) ∧
        ∀ c d, blockIndex C c = blockIndex C d → c < d → w.symm c < w.symm d := by
  unfold IsMinimalRepresentative
  rw [strictMono_index_iff B w, strictMono_index_iff C w.symm]

/-- The canonical block reordering is a minimal representative. -/
theorem isMinimalRepresentative_blockPermutation (B : BlockShape n)
    (e : Equiv.Perm (Fin B.length)) :
    IsMinimalRepresentative B (B.permute e) (B.blockPermutation e) := by
  constructor
  · intro i
    obtain ⟨i, rfl⟩ := e.surjective i
    intro x y hxy
    simp only [BlockShape.blockPermutation_index]
    exact index_strictMono (B.permute e) i hxy
  · intro i x y hxy
    change (B.blockPermutation e).symm ((B.permute e).index i x) <
      (B.blockPermutation e).symm ((B.permute e).index i y)
    rw [B.blockPermutation_symm_index e i x, B.blockPermutation_symm_index e i y]
    exact index_strictMono B (e i) hxy

/-- Minimality survives precomposition with the inverse of a minimal
representative which carries whole source blocks to whole blocks. -/
theorem isMinimalRepresentative_mul_inv {B B' C : BlockShape n}
    {w u : Equiv.Perm (Fin n)} (hw : IsMinimalRepresentative B C w)
    (hu : IsMinimalRepresentative B B' u)
    (hu' : ∀ a b, blockIndex B' (u a) = blockIndex B' (u b) → blockIndex B a = blockIndex B b)
    (hw' : ∀ a b, blockIndex C (w a) = blockIndex C (w b) → blockIndex B a = blockIndex B b) :
    IsMinimalRepresentative B' C (w * u⁻¹) := by
  rw [isMinimalRepresentative_iff] at hw hu ⊢
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hu1, hu2⟩ := hu
  have hs : ∀ c, (w * u⁻¹).symm c = u (w.symm c) := fun c => by
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  constructor
  · intro a b hab hlt
    have h2 : blockIndex B (u.symm a) = blockIndex B (u.symm b) :=
      hu' _ _ (by simpa only [Equiv.apply_symm_apply] using hab)
    exact hw1 _ _ h2 (hu2 a b hab hlt)
  · intro c d hcd hlt
    have h2 : blockIndex B (w.symm c) = blockIndex B (w.symm d) :=
      hw' _ _ (by simpa only [Equiv.apply_symm_apply] using hcd)
    rw [hs, hs]
    exact hu1 _ _ h2 (hw2 c d hcd hlt)

variable {F : Type u} [Field F]

/-- A permutation carrying the blocks of `B` injectively onto blocks of `C`
conjugates the embedded Levi of `B` onto that of `C`. The block map is
recorded through natural-number labels. -/
theorem conjugatesLevi_of_blockIndex {B C : BlockShape n} (w : Equiv.Perm (Fin n))
    (f : Fin B.length → ℕ) (hf : Function.Injective f)
    (h : ∀ a, (blockIndex C (w a) : ℕ) = f (blockIndex B a)) :
    ConjugatesLevi (F := F) B C w := by
  apply Subgroup.ext
  intro g
  rw [Subgroup.mem_map_equiv, levi_mem_iff, levi_mem_iff]
  have hentry : ∀ a b,
      ((MulAut.conj (permutation n F w)).symm g) a b = g (w a) (w b) := by
    intro a b
    rw [MulAut.conj_symm_apply, mul_permutation_entry, permutation_inv,
      permutation_mul_entry, inv_inv]
  have hblock : ∀ a b, blockIndex C (w a) ≠ blockIndex C (w b) ↔
      blockIndex B a ≠ blockIndex B b := by
    intro a b
    rw [Ne, Ne, ← Fin.val_inj, h, h, hf.eq_iff]
  constructor
  · intro hg c d hcd
    have hc := hg (w.symm c) (w.symm d)
      ((hblock _ _).mp (by simpa only [Equiv.apply_symm_apply] using hcd))
    simpa only [hentry, Equiv.apply_symm_apply] using hc
  · intro hg a b hab
    rw [hentry]
    exact hg _ _ ((hblock a b).mpr hab)

/-- The canonical block reordering conjugates the corresponding Levis. -/
theorem conjugatesLevi_blockPermutation (B : BlockShape n)
    (e : Equiv.Perm (Fin B.length)) :
    ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e) :=
  conjugatesLevi_of_blockIndex _ (fun i => (e.symm i : ℕ))
    (Fin.val_injective.comp e.symm.injective)
    (fun a => by rw [blockIndex_blockPermutation])

/-- A Levi-conjugating permutation keeps coordinates of a common source block
in a common target block. -/
theorem blockIndex_eq_of_conjugatesLevi {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) {a b : Fin n}
    (hab : blockIndex B a = blockIndex B b) :
    blockIndex C (w a) = blockIndex C (w b) := by
  have hs : Equiv.swap a b ∈ blockWeyl B := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hab]
    · rw [h2, hab]
    · rfl
  have hc := conjugatesLevi_weyl_mem hw hs (w a)
  rw [← Equiv.swap_apply_apply, Equiv.swap_apply_left] at hc
  exact hc.symm

/-- Coordinates sent to a common target block come from a common source block. -/
theorem blockIndex_eq_of_conjugatesLevi_apply {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F) B C w) {a b : Fin n}
    (hab : blockIndex C (w a) = blockIndex C (w b)) :
    blockIndex B a = blockIndex B b := by
  simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
    blockIndex_eq_of_conjugatesLevi (conjugatesLevi_inv hw) hab

/-- Every Levi-conjugating permutation induces a bijection of block labels;
in particular both shapes have the same number of blocks. The bijection is
recorded through natural-number labels. -/
theorem exists_blockMap_of_conjugatesLevi {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) :
    ∃ e : Equiv.Perm (Fin B.length),
      ∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ) := by
  let g : Fin B.length → Fin C.length := fun i =>
    blockIndex C (w (B.index i ⟨0, B.positive i⟩))
  have hg : ∀ a, blockIndex C (w a) = g (blockIndex B a) := fun a =>
    blockIndex_eq_of_conjugatesLevi hw (by rw [blockIndex_index])
  have hbij : Function.Bijective g := by
    constructor
    · intro i j hij
      have h := blockIndex_eq_of_conjugatesLevi_apply hw hij
      rwa [blockIndex_index, blockIndex_index] at h
    · intro k
      refine ⟨blockIndex B (w.symm (C.index k ⟨0, C.positive k⟩)), ?_⟩
      rw [← hg, Equiv.apply_symm_apply, blockIndex_index]
  have hlen : B.length = C.length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective g hbij)
  refine ⟨((Equiv.ofBijective g hbij).trans (finCongr hlen.symm)).symm, fun a => ?_⟩
  rw [Equiv.symm_symm, hg]
  rfl

end Langlands.CuspidalSupport
