import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Torus.Weights
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Scalar extension of the actual affine Lie kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom]
  (A : Type u) [CommRing A] [Algebra k A]

attribute [local instance] coordinateOriginAlgebra

/-- The base-algebra inclusion is linear for the coordinate action at the identity. -/
def originBaseLinear : k →ₗ[coordinateAlgebra G] A where
  toFun := algebraMap k A
  map_add' := map_add _
  map_smul' c r := by
    change algebraMap k A (coordinateOrigin G c * r) =
      algebraMap k A (coordinateOrigin G c) * algebraMap k A r
    exact map_mul _ _ _

/-- Extend an identity derivation by its scalar-valued coefficients. -/
def identityDerivationBaseMap :
    IdentityDerivation G (A := k) →ₗ[k] IdentityDerivation G (A := A) :=
  (originBaseLinear G A).compDer.restrictScalars k

@[simp]
theorem identityDerivationBaseMap_apply
    (d : IdentityDerivation G (A := k)) (c : coordinateAlgebra G) :
    identityDerivationBaseMap G A d c = algebraMap k A (d c) := rfl

/-- Assemble scalar multiples of identity derivations over the base field. -/
def identityDerivationTensorMap :
    A ⊗[k] IdentityDerivation G (A := k) →ₗ[A]
      IdentityDerivation G (A := A) :=
  (identityDerivationBaseMap G A).liftBaseChange A

@[simp]
theorem identityDerivationTensorMap_tmul (a : A)
    (d : IdentityDerivation G (A := k)) (c : coordinateAlgebra G) :
    identityDerivationTensorMap G A (a ⊗ₜ d) c =
      a * algebraMap k A (d c) := rfl

variable {J : Type u}

/-- A vector-space basis of the test algebra respects the coordinate-origin action. -/
def originBasisLinearEquiv (b : Module.Basis J k A) :
    A ≃ₗ[coordinateAlgebra G] (J →₀ k) where
  toEquiv := b.repr.toEquiv
  map_add' := b.repr.map_add
  map_smul' c a := by
    ext j
    change b.repr (algebraMap k A (coordinateOrigin G c) * a) j =
      coordinateOrigin G c * b.repr a j
    rw [← Algebra.smul_def, map_smul]
    rfl

/-- Extract the finite family of base-field derivations in a test-algebra basis. -/
def identityDerivationBasisCoefficients [LocallyOfFiniteType G.X.hom]
    (b : Module.Basis J k A) :
    IdentityDerivation G (A := A) ≃ₗ[k]
      (J →₀ IdentityDerivation G (A := k)) := by
  have := coordinateAlgebraFiniteType G
  exact ((originBasisLinearEquiv G A b).compDer.trans
    derivationFinsuppLinearEquiv).restrictScalars k

@[simp]
theorem identityDerivationBasisCoefficients_apply [LocallyOfFiniteType G.X.hom]
    (b : Module.Basis J k A) (d : IdentityDerivation G (A := A))
    (j : J) (c : coordinateAlgebra G) :
    identityDerivationBasisCoefficients G A b d j c = b.repr (d c) j := rfl

private theorem identityDerivationTensorMap_coefficients
    [LocallyOfFiniteType G.X.hom] [DecidableEq J] (b : Module.Basis J k A)
    (x : A ⊗[k] IdentityDerivation G (A := k)) :
    identityDerivationBasisCoefficients G A b (identityDerivationTensorMap G A x) =
      TensorProduct.equivFinsuppOfBasisLeft b x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul a d =>
    ext j c
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    change b.repr (a * algebraMap k A (d c)) j = b.repr a j * d c
    rw [mul_comm a, ← Algebra.smul_def, map_smul]
    simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The natural tensor map on identity derivations is bijective over a field. -/
theorem identityDerivationTensorMap_bijective [LocallyOfFiniteType G.X.hom] :
    Function.Bijective (identityDerivationTensorMap G A) := by
  classical
  let b := Module.Free.chooseBasis k A
  constructor
  · intro x y hxy
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    rw [← identityDerivationTensorMap_coefficients G A b,
      ← identityDerivationTensorMap_coefficients G A b, hxy]
  · intro d
    refine ⟨(TensorProduct.equivFinsuppOfBasisLeft b).symm
      (identityDerivationBasisCoefficients G A b d), ?_⟩
    apply (identityDerivationBasisCoefficients G A b).injective
    rw [identityDerivationTensorMap_coefficients, LinearEquiv.apply_symm_apply]

/-- Actual identity derivations commute with arbitrary test-algebra scalar extension. -/
def identityDerivationScalarExtension [LocallyOfFiniteType G.X.hom] :
    A ⊗[k] IdentityDerivation G (A := k) ≃ₗ[A]
      IdentityDerivation G (A := A) :=
  LinearEquiv.ofBijective (identityDerivationTensorMap G A)
    (identityDerivationTensorMap_bijective G A)

/-- Scalar extension of the actual dual-number identity kernel. -/
def kernelScalarExtension [LocallyOfFiniteType G.X.hom] :
    A ⊗[k] Additive (lieKernel G k) ≃ₗ[A] Additive (lieKernel G A) :=
  ((kernelDerivationLinearEquiv G (A := k)).baseChange k A _ _).trans
    ((identityDerivationScalarExtension G A).trans
      (kernelDerivationLinearEquiv G (A := A)).symm)

@[simp]
theorem kernelScalarExtension_tmul [LocallyOfFiniteType G.X.hom]
    (a : A) (x : Additive (lieKernel G k)) :
    kernelScalarExtension G A (a ⊗ₜ x) =
      a • lieKernelMapLinear G (Algebra.ofId k A) x := by
  apply (kernelDerivationLinearEquiv G (A := A)).injective
  ext c
  simp only [kernelScalarExtension, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply,
    identityDerivationScalarExtension, LinearEquiv.ofBijective_apply,
    map_smul]
  change a * algebraMap k A (kernelDerivationEquiv G x.toMul c) =
    a * kernelDerivationEquiv G
      (lieKernelMap G (Algebra.ofId k A) x.toMul) c
  rw [kernelDerivationEquiv_naturality]
  rfl

end Langlands.GroupScheme.Lie
