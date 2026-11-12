import Langlands.GroupScheme.FiniteAlgebraRightRegularWeights
import Langlands.GroupScheme.Quaternionic.GroupSchemes

/-! # Original-algebra equations for affine isometry-cut points -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-- The tensor unit map commutes with the base-changed involution. -/
theorem lid_baseChange (τ : FirstKindInvolution K A) (x : K ⊗[K] A) :
    Algebra.TensorProduct.lid K A (τ.baseChange K x) =
      τ (Algebra.TensorProduct.lid K A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

end FirstKindInvolution

namespace IsometryCut

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] (τ : FirstKindInvolution K A) (Q : A)

/-- An affine base-field point of the zero-subspace isometry cut satisfies
the actual equation in the original algebra. -/
theorem baseAffineUnit_isometry
    (p : (algSpec (CommRingCat.of K)).obj
      (op (CommAlgCat.of (CommRingCat.of K) K)) ⟶
        (groupScheme (τ := τ) (M := ⊥) isStable_bot Q).X) :
    let g := FiniteAlgebraUnits.baseAffineUnit (Module.finBasis K A)
      (p ≫ (inclusion (τ := τ) (M := ⊥) isStable_bot Q).hom.hom)
    (g : A) * Q * τ g = Q := by
  let R := CommAlgCat.of (CommRingCat.of K) K
  let b := Module.finBasis K A
  let x := p ≫ (inclusion (τ := τ) (M := ⊥) isStable_bot Q).hom.hom
  have hx := (mem_range_inclusion_iff (τ := τ) (M := ⊥) isStable_bot Q x).mp
    (SubgroupFunctor.mem_range.mpr ⟨p, rfl⟩)
  rw [Submodule.baseChange_bot, Submodule.mem_bot] at hx
  let f := (Corepresented.affineSectionsIso R).hom.hom
  have hc := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor K A) (FiniteAlgebraUnits.corepresentableBy b) R x
  change Units.map (Algebra.TensorProduct.map f (AlgHom.id K A)).toMonoidHom
    (FiniteAlgebraUnits.pointsEquiv b _ x) =
      FiniteAlgebraUnits.affinePointsEquiv b R x at hc
  have hcval := congrArg Units.val hc
  change Algebra.TensorProduct.map f (AlgHom.id K A)
    (FiniteAlgebraUnits.pointsEquiv b _ x : _) =
      (FiniteAlgebraUnits.affinePointsEquiv b R x : _) at hcval
  have hh := congrArg (Algebra.TensorProduct.map f (AlgHom.id K A)) hx
  rw [map_defect, _root_.map_zero, hcval, defect, sub_eq_zero] at hh
  have hl := congrArg (Algebra.TensorProduct.lid K A) hh
  change
    (Algebra.TensorProduct.lid K A
      (FiniteAlgebraUnits.affinePointsEquiv b R x : K ⊗[K] A)) * Q *
      τ (Algebra.TensorProduct.lid K A
        (FiniteAlgebraUnits.affinePointsEquiv b R x : K ⊗[K] A)) = Q
  simp only [_root_.map_mul, Algebra.TensorProduct.lid_tmul, one_smul] at hl
  change
    (Algebra.TensorProduct.lid K A
      (FiniteAlgebraUnits.affinePointsEquiv b R x : K ⊗[K] A)) * Q *
      Algebra.TensorProduct.lid K A (τ.baseChange K
        (FiniteAlgebraUnits.affinePointsEquiv b R x : K ⊗[K] A)) = Q at hl
  rw [τ.lid_baseChange] at hl
  exact hl

/-- The inverse of such a point satisfies the same isometry equation. -/
theorem baseAffineUnit_inv_isometry
    (p : (algSpec (CommRingCat.of K)).obj
      (op (CommAlgCat.of (CommRingCat.of K) K)) ⟶
        (groupScheme (τ := τ) (M := ⊥) isStable_bot Q).X) :
    let g := FiniteAlgebraUnits.baseAffineUnit (Module.finBasis K A)
      (p ≫ (inclusion (τ := τ) (M := ⊥) isStable_bot Q).hom.hom)
    ((g⁻¹ : Aˣ) : A) * Q * τ (g⁻¹ : Aˣ) = Q := by
  simpa only [GrpObj.inv_comp, _root_.map_inv] using
    baseAffineUnit_isometry τ Q p⁻¹

end IsometryCut

end Langlands.GroupScheme.Quaternionic
