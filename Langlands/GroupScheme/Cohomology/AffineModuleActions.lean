import Langlands.GroupScheme.Cohomology.AffineCochainCoordinates
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Constructing regular module actions from universal affine coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} (M : Type u) [AddCommGroup M] [Module R M]

/-- Coefficient change is semilinear for the full test-algebra scalar action. -/
theorem modulePointMap_smul {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (a : A) (x : ModulePoints M A) :
    modulePointMap M f (a • x) = f.hom a • modulePointMap M f x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    simp only [TensorProduct.smul_tmul', modulePointMap_tmul, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom]

/-- Specialize a universal coefficient coaction at an actual source point and
extend linearly over the test algebra. -/
def universalCoefficientAction
    (c : M →ₗ[R] ModulePoints M (Lie.coordinateAlgebra H))
    (A : CommAlgCat.{u} R) (h : H.affinePoints A) : Module.End A (ModulePoints M A) :=
  ((modulePointMap M (pointSpecialization H h)).comp c).liftBaseChange A

@[simp]
theorem universalCoefficientAction_tmul
    (c : M →ₗ[R] ModulePoints M (Lie.coordinateAlgebra H))
    (A : CommAlgCat.{u} R) (h : H.affinePoints A) (a : A) (m : M) :
    universalCoefficientAction M H c A h (a ⊗ₜ[R] m) =
      a • modulePointMap M (pointSpecialization H h) (c m) := rfl

/-- The specialized coefficient endomorphisms form a natural family before
any group-action laws are imposed. -/
theorem universalCoefficientAction_naturality
    (c : M →ₗ[R] ModulePoints M (Lie.coordinateAlgebra H))
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (h : H.affinePoints A)
    (x : ModulePoints M A) :
    modulePointMap M f (universalCoefficientAction M H c A h x) =
      universalCoefficientAction M H c B (H.affinePointMap f h) (modulePointMap M f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [universalCoefficientAction_tmul, modulePointMap_smul,
      modulePointMap_tmul, universalCoefficientAction_tmul,
      pointSpecialization_naturality, modulePointMap_comp]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The identity and multiplication requirements for a universal coefficient
action, tested at the base identity and the pair of independent generic points. -/
structure UniversalModuleAction where
  coaction : M →ₗ[R] ModulePoints M (Lie.coordinateAlgebra H)
  one (m : M) :
    universalCoefficientAction M H coaction (CommAlgCat.of R R) 1
      ((1 : R) ⊗ₜ[R] m) = (1 : R) ⊗ₜ[R] m
  mul (m : M) :
    universalCoefficientAction M H coaction (pairCoordinateAlgebra H)
        (genericFirst H * genericSecond H) ((1 : pairCoordinateAlgebra H) ⊗ₜ[R] m) =
      universalCoefficientAction M H coaction (pairCoordinateAlgebra H) (genericFirst H)
        (universalCoefficientAction M H coaction (pairCoordinateAlgebra H) (genericSecond H)
          ((1 : pairCoordinateAlgebra H) ⊗ₜ[R] m))

variable {M H}

/-- The universal identity requirement gives the identity endomorphism on every
affine test algebra. -/
theorem UniversalModuleAction.action_one (c : UniversalModuleAction M H)
    (A : CommAlgCat.{u} R) : universalCoefficientAction M H c.coaction A 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    let f : CommAlgCat.of R R ⟶ A := CommAlgCat.ofHom (Algebra.ofId R A)
    have he := congrArg (modulePointMap M f) (c.one m)
    rw [universalCoefficientAction_naturality] at he
    simp only [map_one, modulePointMap, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply] at he
    have htmul : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [htmul]
    change universalCoefficientAction M H c.coaction A 1 (a • ((1 : A) ⊗ₜ[R] m)) = _
    rw [map_smul, he]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The generic-pair multiplication requirement gives the action law on every
affine test algebra, with arbitrary module arguments. -/
theorem UniversalModuleAction.action_mul (c : UniversalModuleAction M H)
    (A : CommAlgCat.{u} R) (h k : H.affinePoints A) :
    universalCoefficientAction M H c.coaction A (h * k) =
      (universalCoefficientAction M H c.coaction A h).comp
        (universalCoefficientAction M H c.coaction A k) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    have he := congrArg (modulePointMap M (pairSpecialization H h k)) (c.mul m)
    rw [universalCoefficientAction_naturality,
      universalCoefficientAction_naturality, universalCoefficientAction_naturality] at he
    simp only [map_mul, genericFirst_specialize, genericSecond_specialize,
      modulePointMap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, map_one] at he
    have htmul : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [htmul]
    change universalCoefficientAction M H c.coaction A (h * k)
        (a • ((1 : A) ⊗ₜ[R] m)) =
      universalCoefficientAction M H c.coaction A h
        (universalCoefficientAction M H c.coaction A k (a • ((1 : A) ⊗ₜ[R] m)))
    rw [map_smul, map_smul, map_smul, he]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The resulting endomorphism-valued point representation. -/
def UniversalModuleAction.endAction (c : UniversalModuleAction M H) (A : CommAlgCat.{u} R) :
    H.affinePoints A →* Module.End A (ModulePoints M A) where
  toFun := universalCoefficientAction M H c.coaction A
  map_one' := c.action_one A
  map_mul' := c.action_mul A

/-- The group inverse makes each constructed coefficient endomorphism an
automorphism, without extra nondegeneracy hypotheses. -/
def UniversalModuleAction.linearAction (c : UniversalModuleAction M H)
    (A : CommAlgCat.{u} R) :
    H.affinePoints A →* (ModulePoints M A ≃ₗ[A] ModulePoints M A) where
  toFun h := LinearEquiv.ofLinearMap (c.endAction A h) (c.endAction A h⁻¹)
    (by change c.endAction A h * c.endAction A h⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
    (by change c.endAction A h⁻¹ * c.endAction A h = 1; rw [← map_mul, inv_mul_cancel, map_one])
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change c.endAction A 1 x = x
    rw [map_one]
    rfl
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    change c.endAction A (h * k) x = c.endAction A h (c.endAction A k x)
    rw [map_mul]
    rfl

/-- A universal coefficient coaction satisfying the two universal tests gives
an actual natural module representation on all affine source points. -/
def UniversalModuleAction.moduleRepresentation (c : UniversalModuleAction M H) :
    ModuleRepresentation M H where
  action A := c.linearAction A
  naturality f h x := universalCoefficientAction_naturality M H c.coaction f h x

end Langlands.GroupScheme.Cohomology
