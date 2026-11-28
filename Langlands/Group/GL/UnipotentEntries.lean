import Langlands.Group.GL.Blocks
import Mathlib.Tactic.NoncommRing

/-!
# Entries of block unipotent radicals

For a block shape `B` of `n` and a commutative ring `R`:

* `BlockShape.upperBlocks R S`: the `S`-submodule of `n × n` matrices over `R` whose blocks on
  and below the diagonal vanish (the Lie algebra of the unipotent radical);
* `BlockShape.mem_unipotentSubgroup_iff_sub_one_mem`: `g ∈ GL_n(R)` lies in the unipotent
  radical of the standard parabolic exactly when `g - 1` lies in `upperBlocks`;
* for at most two blocks, the product of two matrices of `upperBlocks` is `0`, so the unipotent
  radical is commutative (`BlockShape.unipotentSubgroup_mul_comm`);
* a ring endomorphism of `R`, applied entrywise, preserves the unipotent radical.
-/

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

/-- The matrices whose blocks on and below the diagonal vanish: `Y_{xy} = 0` unless the block of
`x` precedes the block of `y`. An `S`-submodule for every `S`-module structure on `R`. -/
def upperBlocks (S : Type*) [Semiring S] [Module S R] : Submodule S (Matrix (Fin n) (Fin n) R) where
  carrier := {Y | ∀ x y : B.Index, ¬ x.1 < y.1 → Y (B.indexEquiv x) (B.indexEquiv y) = 0}
  add_mem' {Y Z} hY hZ x y h := by
    simp only [Set.mem_ofPred_eq] at hY hZ
    rw [Matrix.add_apply, hY x y h, hZ x y h, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c Y hY x y h := by
    simp only [Set.mem_ofPred_eq] at hY
    rw [Matrix.smul_apply, hY x y h, smul_zero]

variable {R} in
theorem mem_upperBlocks {S : Type*} [Semiring S] [Module S R] (Y : Matrix (Fin n) (Fin n) R) :
    Y ∈ B.upperBlocks R S ↔
      ∀ x y : B.Index, ¬ x.1 < y.1 → Y (B.indexEquiv x) (B.indexEquiv y) = 0 :=
  Iff.rfl

/-- `g` lies in the unipotent radical exactly when `g - 1` has vanishing blocks on and below the
diagonal. -/
theorem mem_unipotentSubgroup_iff_sub_one_mem (S : Type*) [Semiring S] [Module S R]
    (g : Langlands.GeneralLinear n R) :
    g ∈ B.unipotentSubgroup R ↔ (g : Matrix (Fin n) (Fin n) R) - 1 ∈ B.upperBlocks R S := by
  rw [B.mem_unipotentSubgroup_iff, B.mem_parabolic_iff, mem_upperBlocks]
  have hne : ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)), i ≠ j →
      (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b) = 0 := by
    intro i j a b hij
    refine Matrix.one_apply_ne fun he => ?_
    exact hij (congrArg Sigma.fst (B.indexEquiv.injective he))
  have hdiag : ∀ (i : Fin B.length) (a b : Fin (B.size i)),
      (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
    intro i a b
    simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨hp, hd⟩ ⟨i, a⟩ ⟨j, b⟩ hij
    rw [Matrix.sub_apply, sub_eq_zero]
    change g (B.index i a) (B.index j b) = (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b)
    rcases lt_trichotomy i j with h | rfl | h
    · exact absurd h hij
    · rw [hd i a b, hdiag]
    · rw [hp i j a b h, hne i j a b h.ne']
  · intro h
    refine ⟨fun i j a b hji => ?_, fun i a b => ?_⟩
    · have h1 := h ⟨i, a⟩ ⟨j, b⟩ (not_lt.2 hji.le)
      rw [Matrix.sub_apply, sub_eq_zero] at h1
      change g (B.index i a) (B.index j b) =
        (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b) at h1
      rw [h1, hne i j a b hji.ne']
    · have h1 := h ⟨i, a⟩ ⟨i, b⟩ (lt_irrefl i)
      rw [Matrix.sub_apply, sub_eq_zero] at h1
      change g (B.index i a) (B.index i b) =
        (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index i b) at h1
      rw [h1, hdiag]

/-- For at most two blocks, the product of two matrices with vanishing blocks on and below the
diagonal is `0`. -/
theorem upperBlocks_mul_eq_zero {S : Type*} [Semiring S] [Module S R] (hB : B.length ≤ 2)
    {Y Z : Matrix (Fin n) (Fin n) R} (hY : Y ∈ B.upperBlocks R S) (hZ : Z ∈ B.upperBlocks R S) :
    Y * Z = 0 := by
  ext p q
  obtain ⟨x, rfl⟩ := B.indexEquiv.surjective p
  obtain ⟨y, rfl⟩ := B.indexEquiv.surjective q
  rw [Matrix.mul_apply, Matrix.zero_apply, ← B.indexEquiv.sum_comp]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hxz : x.1 < z.1
  · by_cases hzy : z.1 < y.1
    · exfalso
      have h1 : x.1.val < z.1.val := hxz
      have h2 : z.1.val < y.1.val := hzy
      have h3 := y.1.isLt
      omega
    · rw [hZ z y hzy, mul_zero]
  · rw [hY x z hxz, zero_mul]

/-- For at most two blocks, the unipotent radical is commutative. -/
theorem unipotentSubgroup_mul_comm (hB : B.length ≤ 2) {a b : Langlands.GeneralLinear n R}
    (ha : a ∈ B.unipotentSubgroup R) (hb : b ∈ B.unipotentSubgroup R) : a * b = b * a := by
  rw [B.mem_unipotentSubgroup_iff_sub_one_mem R R] at ha hb
  have h1 := B.upperBlocks_mul_eq_zero R hB ha hb
  have h2 := B.upperBlocks_mul_eq_zero R hB hb ha
  apply Units.ext
  have e1 : (a : Matrix (Fin n) (Fin n) R) * b = (a - 1) * (b - 1) + a + b - 1 := by noncomm_ring
  have e2 : (b : Matrix (Fin n) (Fin n) R) * a = (b - 1) * (a - 1) + a + b - 1 := by noncomm_ring
  rw [Units.val_mul, Units.val_mul, e1, e2, h1, h2]

/-- A ring endomorphism of `R`, applied to every entry, preserves the unipotent radical. -/
theorem map_mem_unipotentSubgroup (f : R →+* R) {g : Langlands.GeneralLinear n R}
    (hg : g ∈ B.unipotentSubgroup R) :
    Matrix.GeneralLinearGroup.map f g ∈ B.unipotentSubgroup R := by
  rw [B.mem_unipotentSubgroup_iff_sub_one_mem R R] at hg ⊢
  intro x y hxy
  have h := hg x y hxy
  rw [Matrix.sub_apply, sub_eq_zero] at h ⊢
  change f (g (B.indexEquiv x) (B.indexEquiv y)) = _
  rw [h, Matrix.one_apply]
  split_ifs <;> simp

end Langlands.GeneralLinear.BlockShape
