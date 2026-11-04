import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.Geometry.Building.RealTorusAction
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Positive forms on actual real character spaces invariant under the relative Weyl quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped BigOperators

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The actual relative Weyl action on the full real character space. -/
def relativeWeylRealCharacterAction : relativeWeylGroup i →* (Vstar T ≃ₗ[ℝ] Vstar T) :=
  relativeWeylFullRealAction i

@[simp] theorem relativeWeylRealCharacterAction_tmul (w : relativeWeylGroup i)
    (r : ℝ) (χ : characterLattice T) :
    relativeWeylRealCharacterAction i w (r ⊗ₜ[ℤ] χ) =
      r ⊗ₜ[ℤ] (relativeWeylCharacterAction i w χ) := rfl

@[simp] theorem relativeWeylRealCharacterAction_mk (n : normalizerPoints i) :
    relativeWeylRealCharacterAction i (QuotientGroup.mk n) =
      characterRealAut (normalizingAut i n) := rfl

/-- The actual real pairing is invariant under simultaneous quotient actions. -/
theorem pair_relativeWeyl (w : relativeWeylGroup i) (x : Vstar T) (v : V T) :
    pair T (relativeWeylRealCharacterAction i w x) (relativeWeylRealAction i w v) =
      pair T x v :=
  Langlands.GroupScheme.pair_relativeWeyl i w x v

section PositiveForm

variable [Fintype (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)

private def characterBasis (hT : IsSplitTorus T.toGrp) :
    Module.Basis (Fin (Module.finrank ℝ (Vstar T))) ℝ (Vstar T) := by
  let _ := hT.finite_realCharacterSpace
  exact Module.finBasis ℝ (Vstar T)

/-- A noncanonical positive form from finite coordinates of the actual character space. -/
def characterCoordinateForm : LinearMap.BilinForm ℝ (Vstar T) :=
  (dotProductBilin ℝ ℝ).compl₁₂
    (characterBasis hT).equivFun.toLinearMap (characterBasis hT).equivFun.toLinearMap

@[simp] theorem characterCoordinateForm_apply (x y : Vstar T) :
    characterCoordinateForm hT x y =
      ∑ j, (characterBasis hT).equivFun x j * (characterBasis hT).equivFun y j := rfl

theorem characterCoordinateForm_symm (x y : Vstar T) :
    characterCoordinateForm hT x y = characterCoordinateForm hT y x := by
  simp only [characterCoordinateForm_apply, mul_comm]

theorem characterCoordinateForm_nonneg (x : Vstar T) :
    0 ≤ characterCoordinateForm hT x x := by
  rw [characterCoordinateForm_apply]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

theorem characterCoordinateForm_pos {x : Vstar T} (hx : x ≠ 0) :
    0 < characterCoordinateForm hT x x := by
  have hc : (characterBasis hT).equivFun x ≠ 0 := by
    intro h
    exact hx ((characterBasis hT).equivFun.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  rw [characterCoordinateForm_apply]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩

/-- The sum of the pullbacks of a coordinate form by every actual relative Weyl class. -/
def relativeWeylInvariantForm : LinearMap.BilinForm ℝ (Vstar T) :=
  ∑ w : relativeWeylGroup i, (characterCoordinateForm hT).compl₁₂
    (relativeWeylRealCharacterAction i w).toLinearMap
    (relativeWeylRealCharacterAction i w).toLinearMap

@[simp] theorem relativeWeylInvariantForm_apply (x y : Vstar T) :
    relativeWeylInvariantForm i hT x y =
      ∑ w : relativeWeylGroup i,
        characterCoordinateForm hT (relativeWeylRealCharacterAction i w x)
          (relativeWeylRealCharacterAction i w y) := by
  simp [relativeWeylInvariantForm, LinearMap.sum_apply]

theorem relativeWeylInvariantForm_symm (x y : Vstar T) :
    relativeWeylInvariantForm i hT x y = relativeWeylInvariantForm i hT y x := by
  rw [relativeWeylInvariantForm_apply, relativeWeylInvariantForm_apply]
  exact Finset.sum_congr rfl (fun w _ => characterCoordinateForm_symm hT _ _)

theorem relativeWeylInvariantForm_nonneg (x : Vstar T) :
    0 ≤ relativeWeylInvariantForm i hT x x := by
  rw [relativeWeylInvariantForm_apply]
  exact Finset.sum_nonneg fun w _ => characterCoordinateForm_nonneg hT _

theorem relativeWeylInvariantForm_pos {x : Vstar T} (hx : x ≠ 0) :
    0 < relativeWeylInvariantForm i hT x x := by
  rw [relativeWeylInvariantForm_apply]
  refine Finset.sum_pos' (fun w _ => characterCoordinateForm_nonneg hT _) ?_
  refine ⟨1, Finset.mem_univ _, ?_⟩
  rw [map_one]
  change 0 < characterCoordinateForm hT x x
  exact characterCoordinateForm_pos hT hx

/-- Right multiplication permutes the sum, giving simultaneous Weyl invariance. -/
theorem relativeWeylInvariantForm_invariant (z : relativeWeylGroup i) (x y : Vstar T) :
    relativeWeylInvariantForm i hT (relativeWeylRealCharacterAction i z x)
      (relativeWeylRealCharacterAction i z y) = relativeWeylInvariantForm i hT x y := by
  simp only [relativeWeylInvariantForm_apply]
  simp_rw [← LinearEquiv.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight z) _ _ (fun _ => rfl)

/-- No nonzero actual real character is annihilated by the constructed form. -/
theorem relativeWeylInvariantForm_separatingLeft :
    (relativeWeylInvariantForm i hT).SeparatingLeft := by
  intro x hx
  by_contra h
  have hp := relativeWeylInvariantForm_pos i hT h
  exact (ne_of_gt hp) (hx x)

end PositiveForm

end Langlands.GroupScheme.RealTorusSpace
