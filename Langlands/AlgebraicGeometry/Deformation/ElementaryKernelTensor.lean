import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantIdeal
import Langlands.AlgebraicGeometry.Deformation.ArtinianElementaryKernel
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Actual elementary kernels after flat scalar extension -/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor

section Ideal

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
  (I : Ideal A)

lemma idealTensorMap_injective [Module.Flat A R] :
    Function.Injective (GroupoidCoaction.idealTensorMap (C := R) I) :=
  (TensorProduct.AlgebraTensorModule.rid A R R).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.subtype_injective)

/-- Flat extension identifies the tensor of an ideal with its actual extended ideal. -/
def idealTensorEquiv [Module.Flat A R] :
    R ⊗[A] I ≃ₗ[R] I.map (algebraMap A R) :=
  (LinearEquiv.ofInjective (GroupoidCoaction.idealTensorMap I) (idealTensorMap_injective I)).trans
    (LinearEquiv.ofEq _ _ (GroupoidCoaction.range_idealTensorMap I))

@[simp]
lemma idealTensorEquiv_tmul [Module.Flat A R] (r : R) (x : I) :
    (idealTensorEquiv (R := R) I (r ⊗ₜ[A] x)).val = algebraMap A R x.val * r := by
  change GroupoidCoaction.idealTensorMap I (r ⊗ₜ[A] x) = _
  exact GroupoidCoaction.idealTensorMap_tmul I r x

end Ideal

section Coefficients

variable {A K R M : Type u} [CommRing A] [CommRing K] [CommRing R]
  [Algebra A K] [Algebra A R] [AddCommGroup M] [Module A M] [Module K M]
  [IsScalarTower A K M]

local instance : Algebra R (K ⊗[A] R) := Algebra.TensorProduct.rightAlgebra

private def coefficientTensorEquivAux :
    (K ⊗[A] R) ⊗[K] M ≃ₗ[A] R ⊗[A] M :=
  (((TensorProduct.comm K (K ⊗[A] R) M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A K K M R)).restrictScalars A).trans
      (TensorProduct.comm A M R)

private lemma coefficientTensorEquivAux_tmul (c : K) (r : R) (x : M) :
    coefficientTensorEquivAux ((c ⊗ₜ[A] r) ⊗ₜ[K] x) = r ⊗ₜ[A] (c • x) := rfl

/-- Tensoring a residue-module coefficient on the actual fibre ring agrees with
tensoring that coefficient on the original algebra. -/
def coefficientTensorEquiv :
    (K ⊗[A] R) ⊗[K] M ≃ₗ[R] R ⊗[A] M :=
  { coefficientTensorEquivAux.toAddEquiv with
    map_smul' := by
      intro s t
      change coefficientTensorEquivAux (s • t) = s • coefficientTensorEquivAux t
      induction t using TensorProduct.inductionOn with
      | tmul y x =>
        induction y using TensorProduct.inductionOn with
        | tmul c r =>
          simp [TensorProduct.smul_tmul', Algebra.smul_def,
            Algebra.TensorProduct.right_algebraMap_apply,
            coefficientTensorEquivAux_tmul]
        | add a b ha hb =>
          simpa only [smul_add, TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb
      | add a b ha hb =>
        simpa only [smul_add, map_add] using congrArg₂ (· + ·) ha hb }

@[simp]
lemma coefficientTensorEquiv_tmul (c : K) (r : R) (x : M) :
    coefficientTensorEquiv ((c ⊗ₜ[A] r) ⊗ₜ[K] x) = r ⊗ₜ[A] (c • x) := rfl

@[simp]
lemma coefficientTensorEquiv_symm_tmul (r : R) (x : M) :
    coefficientTensorEquiv.symm (r ⊗ₜ[A] x) = (1 ⊗ₜ[A] r) ⊗ₜ[K] x := rfl

end Coefficients

section Elementary

open ArtinianTest ArtinianTest.ElementaryKernel

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {A B : ArtinianTest k K} (q : A ⟶ B) [he : Fact (IsElementarySurjection q)]
  {R : Type u} [CommRing R] [Algebra A.algebra R]

local notation "hq" => he.out

local instance : Algebra A.algebra K := A.augmentation.toRingHom.toAlgebra
local instance : Module K (Kernel q) := residueModule q hq
local instance : IsScalarTower A.algebra K (Kernel q) :=
  IsScalarTower.of_algebraMap_smul (augmentation_smul q hq)
local instance : Algebra R (K ⊗[A.algebra] R) := Algebra.TensorProduct.rightAlgebra

/-- The actual elementary ideal after flat extension is the fibre coefficient
tensor of the unchanged residue-field kernel. -/
def kernelTensorEquiv [Module.Flat A.algebra R] :
    (K ⊗[A.algebra] R) ⊗[K] Kernel q ≃ₗ[R]
      (Kernel q).map (algebraMap A.algebra R) :=
  coefficientTensorEquiv.trans (idealTensorEquiv (Kernel q))

@[simp]
lemma kernelTensorEquiv_tmul [Module.Flat A.algebra R] (c : K) (r : R) (x : Kernel q) :
    (kernelTensorEquiv q ((c ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val =
      algebraMap A.algebra R (c • x).val * r := by
  simp [kernelTensorEquiv]

@[simp]
lemma kernelTensorEquiv_one_tmul [Module.Flat A.algebra R] (r : R) (x : Kernel q) :
    (kernelTensorEquiv q ((1 ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val =
      algebraMap A.algebra R x.val * r := by
  simp

end Elementary

end Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor
