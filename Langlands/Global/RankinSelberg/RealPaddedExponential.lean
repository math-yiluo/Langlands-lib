import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Langlands.Geometry.Manifold.LinearLieGroup.Exponential
import Mathlib.Algebra.Group.Pi.Units

/-! # Exponential lines for the real leading block homomorphisms -/

noncomputable section

open scoped Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPaddedExponential

open NormedSpace (exp)

local notation "M" => fun n : ℕ => Matrix (Fin n) (Fin n) ℝ
local notation "G" => fun n : ℕ => Langlands.GeneralLinear n ℝ

private def diagonalBlocks {m k n : ℕ} (h : m + k = n) : (M m × M k) →+* M n :=
  (Matrix.reindexAlgEquiv ℝ ℝ (finSumFinEquiv.trans (finCongr h))).toRingHom.comp
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_zero' := Matrix.fromBlocks_zero
      map_one' := Matrix.fromBlocks_one
      map_add' := fun p q => by rw [Matrix.fromBlocks_add]; simp
      map_mul' := fun p q => by rw [Matrix.fromBlocks_multiply]; simp }

private theorem diagonalBlocks_apply {m k n : ℕ} (h : m + k = n) (p : M m × M k) :
    diagonalBlocks h p = Matrix.reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks p.1 0 0 p.2) := rfl

private theorem continuous_diagonalBlocks {m k n : ℕ} (h : m + k = n) : Continuous (diagonalBlocks h) :=
  (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_reindex _ _

private theorem diagonalBlocks_smul {m k n : ℕ} (h : m + k = n) (t : ℝ) (p : M m × M k) :
    diagonalBlocks h (t • p) = t • diagonalBlocks h p := by
  rw [diagonalBlocks_apply, diagonalBlocks_apply]
  change Matrix.reindexLinearEquiv ℝ ℝ _ _ (Matrix.fromBlocks (t • p.1) 0 0 (t • p.2)) =
    t • Matrix.reindexLinearEquiv ℝ ℝ _ _ (Matrix.fromBlocks p.1 0 0 p.2)
  rw [← map_smul, Matrix.fromBlocks_smul, smul_zero, smul_zero]

/-- Insert the Lie direction in the first block and zero in the remaining block. -/
def padLie {m n : ℕ} (h : m ≤ n) : M m →ₗ[ℝ] M n where
  toFun X := diagonalBlocks (Nat.add_sub_of_le h) (X, 0)
  map_add' X Y := by
    rw [← map_add]
    simp
  map_smul' t X := by
    change diagonalBlocks (Nat.add_sub_of_le h) (t • X, 0) = t • diagonalBlocks (Nat.add_sub_of_le h) (X, 0)
    rw [← diagonalBlocks_smul]
    simp

private theorem exp_matrix_pair_zero {m k : ℕ} (X : M m) : exp ((X, 0) : M m × M k) = (exp X, 1) := by
  apply Prod.ext
  · exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (RingHom.fst (M m) (M k)) continuous_fst
      (X, 0)
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  · change (exp ((X, 0) : M m × M k)).2 = (1 : M k)
    rw [← NormedSpace.exp_zero (𝔸 := M k)]
    exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (RingHom.snd (M m) (M k)) continuous_snd
      (X, 0)
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)

/-- Padding an exponential by the identity exponentiates the Lie direction padded by zero. -/
theorem padGL_expUnit {m n : ℕ} (h : m ≤ n) (X : M m) :
    padGL h (Langlands.LinearLieGroup.expUnit (M m) X) = Langlands.LinearLieGroup.expUnit (M n) (padLie h X) := by
  apply Units.ext
  let f := diagonalBlocks (Nat.add_sub_of_le h)
  change f (exp X, 1) = exp (f (X, 0))
  rw [← exp_matrix_pair_zero (k := n - m)]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) f (continuous_diagonalBlocks (Nat.add_sub_of_le h))
    (X, 0)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)

variable {ι : Type*} [Fintype ι] {m : ℕ} (n : ι → ℕ) (h : ∀ i, m ≤ n i)

/-- The simultaneous leading-block homomorphism into a family of real general linear groups. -/
def padProductGL : G m →* (∀ i, M (n i))ˣ :=
  MulEquiv.piUnits.symm.toMonoidHom.comp (MonoidHom.pi fun i => padGL (h i))

/-- The simultaneous leading-block map on Lie directions. -/
def padProductLie : M m →ₗ[ℝ] (∀ i, M (n i)) := LinearMap.pi fun i => padLie (h i)

/-- The simultaneous leading-block homomorphism is continuous. -/
theorem continuous_padProductGL : Continuous (padProductGL n h) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous (fun g : G m => (padGL (h i) g).val)
  exact Units.continuous_val.comp (UnequalAnalytic.continuous_padGL (h i))

/-- The simultaneous padding sends ambient exponential lines to the exponentials of their
simultaneously padded Lie directions. -/
def RealPaddedProductExponentialStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] {m : ℕ} (n : ι → ℕ) (h : ∀ i, m ≤ n i),
    Continuous (padProductGL n h) ∧
      ∀ X : M m, padProductGL n h (Langlands.LinearLieGroup.expUnit (M m) X) =
        Langlands.LinearLieGroup.expUnit (∀ i, M (n i)) (padProductLie n h X)

theorem realPaddedProductExponential : RealPaddedProductExponentialStatement := by
  intro ι _ m n h
  refine ⟨continuous_padProductGL n h, fun X => ?_⟩
  apply Units.ext
  funext i
  change (padGL (h i) (Langlands.LinearLieGroup.expUnit (M m) X)).val = exp (padProductLie n h X) i
  rw [padGL_expUnit, Langlands.LinearLieGroup.coe_expUnit]
  exact (NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (Pi.evalRingHom (fun j => M (n j)) i)
    (continuous_apply i) (x := padProductLie n h X)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)).symm

end Langlands.Global.RankinSelbergGlobal.RealPaddedExponential
