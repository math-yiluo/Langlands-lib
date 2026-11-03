import Langlands.GroupScheme.Rational.CoordinateLieComparisonStatement

/-! # Augmentation cotangent duality for the actual Lie kernel -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

namespace AugmentedAlgebra

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (p : C →ₐ[R] R)

abbrev ideal : Ideal C := RingHom.ker p.toRingHom

/-- Remove the constant part of an element of an augmented algebra. -/
def project : C →ₗ[R] ideal p where
  toFun c := ⟨c - algebraMap R C (p c), by simp⟩
  map_add' x y := by ext; simp [map_add, add_sub_add_comm]
  map_smul' r x := by
    ext
    simp [Algebra.smul_def, mul_sub]

/-- The universal augmentation class. -/
def classMap : C →ₗ[R] (ideal p).Cotangent :=
  ((ideal p).toCotangent.restrictScalars R).comp (project p)

@[simp] theorem classMap_ideal (x : ideal p) :
    classMap p x = (ideal p).toCotangent x := by
  change (ideal p).toCotangent (project p x) = _
  congr 1
  ext
  change (x : C) - algebraMap R C (p x) = x
  rw [show p x = 0 from x.property, map_zero, sub_zero]

@[simp] theorem classMap_algebraMap (r : R) :
    classMap p (algebraMap R C r) = 0 := by
  change (ideal p).toCotangent (project p (algebraMap R C r)) = 0
  convert (ideal p).toCotangent.map_zero
  ext
  simp [project]

/-- The first-order product rule in the augmentation quotient. -/
theorem classMap_mul (x y : C) :
    classMap p (x * y) = p x • classMap p y + p y • classMap p x := by
  change (ideal p).toCotangent (project p (x * y)) =
    p x • (ideal p).toCotangent (project p y) +
      p y • (ideal p).toCotangent (project p x)
  calc
    _ = (ideal p).toCotangent (p x • project p y + p y • project p x) := by
      rw [Ideal.toCotangent_eq, pow_two]
      have h : (project p (x * y) : C) - ((p x • project p y + p y • project p x : ideal p) : C) =
          (project p x : C) * (project p y : C) := by
        simp only [project, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
          Submodule.coe_add, Submodule.coe_smul_of_tower, map_mul, Algebra.smul_def]
        ring
      rw [h]
      exact Ideal.mul_mem_mul (project p x).property (project p y).property
    _ = _ := by simp only [map_add, LinearMap.map_smul_of_tower]

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hp : ∀ c, algebraMap C A c = algebraMap R A (p c))

/-- Restrict a derivation at the augmentation to its quotient by products. -/
def descend (d : Derivation R C A) : (ideal p).Cotangent →ₗ[R] A :=
  Ideal.Cotangent.lift (d.toLinearMap.comp ((ideal p).subtype.restrictScalars R)) (by
    intro x y
    change d ((x : C) * y) = 0
    rw [d.leibniz, Algebra.smul_def, Algebra.smul_def, hp, hp,
      show p x = 0 from x.property, show p y = 0 from y.property]
    simp)

@[simp] theorem descend_mk (d : Derivation R C A) (x : ideal p) :
    descend p hp d ((ideal p).toCotangent x) = d x := rfl

/-- A functional on the augmentation quotient differentiates by removing constants. -/
def ascend (f : (ideal p).Cotangent →ₗ[R] A) : Derivation R C A where
  toLinearMap := f.comp (classMap p)
  map_one_eq_zero' := by
    change f (classMap p 1) = 0
    simpa using congrArg f (classMap_algebraMap p (1 : R))
  leibniz' x y := by
    simp only [LinearMap.comp_apply, classMap_mul, map_add, map_smul]
    simp only [Algebra.smul_def, hp]

/-- Derivations at a split augmentation are precisely functionals on I/I². -/
def duality : Derivation R C A ≃ₗ[A] ((ideal p).Cotangent →ₗ[R] A) where
  toFun := descend p hp
  invFun := ascend p hp
  left_inv d := by
    ext c
    change d (c - algebraMap R C (p c)) = d c
    rw [map_sub, d.map_algebraMap, sub_zero]
  right_inv f := by
    ext q
    obtain ⟨x, rfl⟩ := (ideal p).toCotangent_surjective q
    change f (classMap p x) = f ((ideal p).toCotangent x)
    rw [classMap_ideal]
  map_add' d e := by
    ext q
    obtain ⟨x, rfl⟩ := (ideal p).toCotangent_surjective q
    rfl
  map_smul' a d := by
    ext q
    obtain ⟨x, rfl⟩ := (ideal p).toCotangent_surjective q
    rfl

end AugmentedAlgebra

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (A : Type u) [CommRing A] [Algebra k A]

attribute [local instance] Lie.coordinateOriginAlgebra

/-- Actual identity-kernel vectors are the dual of the actual augmentation quotient. -/
def kernelCotangentEquiv : Additive (lieKernel G A) ≃ₗ[A] (Cotangent G →ₗ[k] A) :=
  (Lie.kernelDerivationLinearEquiv G).trans
    (AugmentedAlgebra.duality (Lie.coordinateOrigin G) (fun _ => rfl))

@[simp] theorem kernelCotangentEquiv_mk (X : Additive (lieKernel G A)) (f : augmentation G) :
    kernelCotangentEquiv G A X (cotangentMk G f) =
      Lie.kernelDerivationEquiv G X.toMul f.val := rfl

/-- The first exact comparison target, at every universe and coefficient algebra. -/
theorem kernelCotangentDuality : KernelCotangentDualityStatement.{u} := by
  intro k _ G hAff
  letI := hAff
  intro A _ _
  exact ⟨kernelCotangentEquiv G A, kernelCotangentEquiv_mk G A⟩

end Langlands.GroupScheme.CoordinateWeights
