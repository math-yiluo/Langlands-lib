import Langlands.ClassField.Global.FullLogUnitLattice
import Mathlib.Algebra.Group.Action.Units
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # Arithmetic equivariance of the full logarithm and its image lattice -/

noncomputable section

open NumberField NumberField.InfinitePlace
open scoped Classical

attribute [local instance] Units.mulDistribMulActionRight

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]

/-- Arithmetic permutations act on full real coordinates by inverse precomposition. -/
def fullLogPermutation : (E ≃ₐ[F] E) →*
    ((InfinitePlace E → ℝ) ≃ₗ[ℝ] (InfinitePlace E → ℝ)) where
  toFun g := LinearEquiv.funCongrLeft ℝ ℝ (MulAction.toPerm (g⁻¹))
  map_one' := by ext x w; simp
  map_mul' g h := by ext x w; simp [mul_smul]

@[simp] theorem fullLogPermutation_apply (g : E ≃ₐ[F] E)
    (x : InfinitePlace E → ℝ) (w : InfinitePlace E) :
    fullLogPermutation F E g x w = x (g⁻¹ • w) := rfl

/-- The arithmetic action preserves the real or complex multiplicity of a place. -/
theorem infinitePlace_mult_smul (g : E ≃ₐ[F] E) (w : InfinitePlace E) :
    mult (g • w) = mult w := by
  simp only [mult, isReal_smul_iff]

/-- The ordinary arithmetic action on actual units has the expected field value. -/
@[simp] theorem unit_smul_coe (g : E ≃ₐ[F] E) (x : (𝓞 E)ˣ) :
    ((g • x : (𝓞 E)ˣ) : E) = g (x : E) := rfl

/-- Full normalized logarithms intertwine the actual unit action and the place permutation. -/
theorem fullLogEmbedding_equivariant (g : E ≃ₐ[F] E) (x : (𝓞 E)ˣ) :
    fullLogEmbedding E (Additive.ofMul (g • x)) =
      fullLogPermutation F E g (fullLogEmbedding E (Additive.ofMul x)) := by
  funext w
  simp only [fullLogEmbedding_apply, fullLogPermutation_apply,
    infinitePlace_mult_smul, InfinitePlace.smul_apply, unit_smul_coe]
  rfl

variable [NumberField E]

/-- Coordinate sum is invariant under the arithmetic permutations. -/
theorem infiniteLogSum_permutation (g : E ≃ₐ[F] E) (x : InfinitePlace E → ℝ) :
    infiniteLogSum E (fullLogPermutation F E g x) = infiniteLogSum E x := by
  exact Equiv.sum_comp (MulAction.toPerm (g⁻¹)) x

theorem fullLogPermutation_mem_hyperplane (g : E ≃ₐ[F] E) (x : InfinitePlace E → ℝ) :
    fullLogPermutation F E g x ∈ fullLogHyperplane E ↔ x ∈ fullLogHyperplane E := by
  change infiniteLogSum E (fullLogPermutation F E g x) = 0 ↔ infiniteLogSum E x = 0
  rw [infiniteLogSum_permutation]

/-- The arithmetic permutation action restricted to the sum-zero hyperplane. -/
def fullLogHyperplaneAut : (E ≃ₐ[F] E) →*
    (fullLogHyperplane E ≃ₗ[ℝ] fullLogHyperplane E) where
  toFun g :=
    { toFun := fun x => ⟨fullLogPermutation F E g x, (fullLogPermutation_mem_hyperplane
        F E g x).mpr x.2⟩
      invFun := fun x => ⟨fullLogPermutation F E g⁻¹ x, (fullLogPermutation_mem_hyperplane
        F E g⁻¹ x).mpr x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by ext x w; simp
  map_mul' g h := by ext x w; simp

@[simp] theorem fullLogHyperplaneAut_apply (g : E ≃ₐ[F] E) (x : fullLogHyperplane E) :
    (fullLogHyperplaneAut F E g x : InfinitePlace E → ℝ) = fullLogPermutation F E g x := rfl

theorem fullLogEmbeddingToHyperplane_equivariant (g : E ≃ₐ[F] E) (x : (𝓞 E)ˣ) :
    fullLogEmbeddingToHyperplane E (Additive.ofMul (g • x)) =
      fullLogHyperplaneAut F E g (fullLogEmbeddingToHyperplane E (Additive.ofMul x)) := by
  apply Subtype.ext
  exact fullLogEmbedding_equivariant F E g x

/-- The image lattice is stable under the genuine arithmetic action. -/
theorem fullLogUnitLattice_invariant (g : E ≃ₐ[F] E) (y : fullLogHyperplane E)
    (hy : y ∈ fullLogUnitLattice E) :
    fullLogHyperplaneAut F E g y ∈ fullLogUnitLattice E := by
  obtain ⟨x, rfl⟩ := (mem_fullLogUnitLattice E y).mp hy
  apply (mem_fullLogUnitLattice E _).mpr
  exact ⟨Additive.ofMul (g • x.toMul), fullLogEmbeddingToHyperplane_equivariant F E g x.toMul⟩

end Langlands.ClassField.Global
