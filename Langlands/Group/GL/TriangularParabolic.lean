import Langlands.Group.GL.Blocks
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Langlands.GeneralLinear

universe u

/-- The actual subgroup of upper triangular invertible matrices. -/
def upperTriangularSubgroup (n : ℕ) (R : Type u) [CommRing R] :
    Subgroup (Langlands.GeneralLinear n R) where
  carrier := {g | g.val.IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := ha.mul hb
  inv_mem' := by
    intro g hg
    let := g.invertible
    change (g⁻¹).val.IsUpperTriangular
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

@[simp]
theorem mem_upperTriangularSubgroup_iff {n : ℕ} {R : Type u} [CommRing R]
    (g : Langlands.GeneralLinear n R) :
    g ∈ upperTriangularSubgroup n R ↔ ∀ i j : Fin n, j < i → g i j = 0 := by
  rfl

end Langlands.GeneralLinear

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n)

/-- Consecutive coordinates in earlier blocks precede every coordinate in later blocks. -/
theorem index_lt_index_of_block_lt {i j : Fin B.length}
    (hij : i < j) (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.index i a < B.index j b := by
  have hprefix :
      (∑ k : Fin (i.val + 1), B.size (Fin.castLE i.isLt k)) ≤
        ∑ k : Fin j.val, B.size (Fin.castLE j.isLt.le k) := by
    apply Finset.sum_le_sum_of_injOn (Fin.castLE (show i.val + 1 ≤ j.val from hij))
    · intro x _ y _ h
      exact Fin.ext (congrArg (fun k : Fin j.val => k.val) h)
    · exact Finset.subset_univ _
    · intro k _
      exact le_rfl
    · intro k _ _
      exact Nat.zero_le _
  have hp :
      (∑ k : Fin (i.val + 1), B.size (Fin.castLE i.isLt k)) =
        (∑ k : Fin i.val, B.size (Fin.castLE i.isLt.le k)) + B.size i := by
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hp] at hprefix
  change (B.indexEquiv ⟨i, a⟩).val < (B.indexEquiv ⟨j, b⟩).val
  simp only [indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  omega

/-- Every invertible upper triangular matrix lies in the standard block parabolic. -/
theorem mem_parabolic_of_isUpperTriangular {R : Type*} [CommRing R]
    (g : Langlands.GeneralLinear n R) (hg : g.val.IsUpperTriangular) :
    g ∈ B.parabolic R := by
  rw [B.mem_parabolic_iff]
  intro i j a b hji
  exact hg (B.index_lt_index_of_block_lt hji b a)

end Langlands.GeneralLinear.BlockShape

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

/-- The upper triangular subgroup is contained in every standard block parabolic. -/
theorem upperTriangularSubgroup_le_parabolic :
    upperTriangularSubgroup n R ≤ B.parabolic R := by
  intro g hg
  exact B.mem_parabolic_of_isUpperTriangular g hg

/-- The inclusion of actual upper triangular matrices into an actual block parabolic. -/
def upperTriangularInParabolic : upperTriangularSubgroup n R →* B.parabolic R :=
  Subgroup.inclusion (B.upperTriangularSubgroup_le_parabolic R)

@[simp]
theorem upperTriangularInParabolic_val (g : upperTriangularSubgroup n R) :
    (B.upperTriangularInParabolic R g).val = g.val := rfl

/-- The parabolic inclusion retains every matrix. -/
theorem upperTriangularInParabolic_injective :
    Function.Injective (B.upperTriangularInParabolic R) := by
  intro g h hgh
  exact Subtype.ext (congrArg (fun x : B.parabolic R => x.val) hgh)

end Langlands.GeneralLinear.BlockShape
