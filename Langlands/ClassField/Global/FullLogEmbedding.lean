import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! # Full logarithmic coordinates for number-field units -/

noncomputable section

open NumberField NumberField.InfinitePlace
open scoped BigOperators

namespace Langlands.ClassField.Global

universe v

variable (E : Type v) [Field E] [NumberField E]

/-- Sum of all real infinite-place coordinates. -/
def infiniteLogSum : (InfinitePlace E → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x w
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact Finset.smul_sum.symm

/-- The hyperplane of full infinite-place coordinates whose sum is zero. -/
def fullLogHyperplane : Submodule ℝ (InfinitePlace E → ℝ) :=
  LinearMap.ker (infiniteLogSum E)

@[simp] theorem mem_fullLogHyperplane (x : InfinitePlace E → ℝ) :
    x ∈ fullLogHyperplane E ↔ ∑ w, x w = 0 := Iff.rfl

/-- Weighted logarithms at every infinite place, including Mathlib's omitted place. -/
def fullLogEmbedding : Additive (𝓞 E)ˣ →+ (InfinitePlace E → ℝ) where
  toFun x w := mult w * Real.log (w (x.toMul : E))
  map_zero' := by simp; rfl
  map_add' x y := by simp [Real.log_mul, mul_add]; rfl

omit [NumberField E] in
@[simp] theorem fullLogEmbedding_apply (x : (𝓞 E)ˣ) (w : InfinitePlace E) :
    fullLogEmbedding E (Additive.ofMul x) w = mult w * Real.log (w (x : E)) := rfl

/-- The product formula places the full logarithm in the sum-zero hyperplane. -/
theorem fullLogEmbedding_mem (x : Additive (𝓞 E)ˣ) :
    fullLogEmbedding E x ∈ fullLogHyperplane E := by
  rw [mem_fullLogHyperplane]
  exact NumberField.Units.sum_mult_mul_log x.toMul

/-- The full logarithm with its codomain restricted to the actual hyperplane. -/
def fullLogEmbeddingToHyperplane : Additive (𝓞 E)ˣ →+ fullLogHyperplane E :=
  (fullLogEmbedding E).codRestrict (fullLogHyperplane E).toAddSubgroup
    (fullLogEmbedding_mem E)

/-- Forgetting the distinguished coordinate identifies the hyperplane with
Mathlib's logarithmic space; the missing coordinate is minus the sum of the others. -/
def fullLogHyperplaneEquiv : fullLogHyperplane E ≃ₗ[ℝ]
    NumberField.Units.dirichletUnitTheorem.logSpace E := by
  classical
  let w₀ : InfinitePlace E := NumberField.Units.dirichletUnitTheorem.w₀
  exact
    { toFun := fun x w => x.1 w.1
      invFun := fun x =>
        ⟨fun w => if h : w = w₀ then -∑ z, x z else x ⟨w, h⟩, by
          rw [mem_fullLogHyperplane, Fintype.sum_eq_add_sum_subtype_ne _ w₀]
          simp only
          have hsum : (∑ z : {w : InfinitePlace E // w ≠ w₀},
              if h : z.1 = w₀ then -∑ z, x z else x ⟨z.1, h⟩) = ∑ z, x z := by
            apply Finset.sum_congr rfl
            intro z _
            simp only [dite_eq_right z.2]
            rfl
          rw [hsum]
          exact neg_add_cancel _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext w
        by_cases hw : w = w₀
        · subst w
          have hx := (mem_fullLogHyperplane E x.1).mp x.2
          rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hx
          simp only
          exact (eq_neg_of_add_eq_zero_left hx).symm
        · simp [hw]
      right_inv := by
        intro x
        funext w
        exact dite_eq_right w.2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem fullLogHyperplaneEquiv_apply (x : fullLogHyperplane E)
    (w : {w : InfinitePlace E // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    fullLogHyperplaneEquiv E x w = x.1 w.1 := rfl

/-- The full logarithm restricts exactly to Mathlib's existing unit logarithm. -/
theorem fullLogHyperplaneEquiv_log (x : Additive (𝓞 E)ˣ) :
    fullLogHyperplaneEquiv E (fullLogEmbeddingToHyperplane E x) =
      NumberField.Units.logEmbedding E x := rfl

/-- The kernel of the full logarithm is precisely the torsion subgroup of units. -/
theorem fullLogEmbedding_eq_zero_iff (x : (𝓞 E)ˣ) :
    fullLogEmbedding E (Additive.ofMul x) = 0 ↔ x ∈ NumberField.Units.torsion E := by
  constructor
  · intro h
    apply NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp
    funext w
    exact congrFun h w.1
  · intro h
    funext w
    have hw := (NumberField.Units.mem_torsion E).mp h w
    simp [hw]

theorem fullLogEmbedding_ker :
    (fullLogEmbedding E).ker = (NumberField.Units.torsion E).toAddSubgroup := by
  ext x
  exact fullLogEmbedding_eq_zero_iff E x.toMul

end Langlands.ClassField.Global
