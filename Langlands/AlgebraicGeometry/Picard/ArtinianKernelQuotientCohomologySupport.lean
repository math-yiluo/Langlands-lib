import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientTensorNaturality
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite coefficient subspaces killing actual ideal-cohomology classes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomologySupport

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueCohomology ArtinianKernelQuotientTensorNaturality

section TensorCoefficients

variable {K H V V' η : Type u} [Field K]
  [AddCommGroup H] [Module K H] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [Finite η] (e : Module.Basis η K H)

/-- Coordinates of a tensor in a basis of its cohomology factor. -/
def tensorCoefficients (t : H ⊗[K] V) : η → V :=
  vectorTensorCoordinates e (TensorProduct.comm K H V t)

/-- The span in the coefficient space of all coefficients of a tensor. -/
def tensorCoefficientSubspace (t : H ⊗[K] V) : Submodule K V :=
  Submodule.span K (Set.range (tensorCoefficients e t))

lemma tensorCoefficients_map (ψ : V →ₗ[K] V') (t : H ⊗[K] V) (j : η) :
    tensorCoefficients e (TensorProduct.map LinearMap.id ψ t) j =
      ψ (tensorCoefficients e t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul x v =>
    simp only [tensorCoefficients, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.comm_tmul, vectorTensorCoordinates_tmul, map_smul]
  | add x y hx hy =>
    simpa only [tensorCoefficients, map_add, LinearEquiv.map_add, Pi.add_apply]
      using congrArg₂ (· + ·) hx hy

lemma tensor_map_eq_zero_iff_coefficients (ψ : V →ₗ[K] V') (t : H ⊗[K] V) :
    TensorProduct.map LinearMap.id ψ t = 0 ↔ ∀ j, ψ (tensorCoefficients e t j) = 0 := by
  constructor
  · intro ht j
    have h := congrArg (fun z => tensorCoefficients e z j) ht
    rw [tensorCoefficients_map e] at h
    simpa only [tensorCoefficients, map_zero, LinearEquiv.map_zero, Pi.zero_apply] using h
  · intro ht
    apply (TensorProduct.comm K H V').injective
    apply (vectorTensorCoordinates e).injective
    ext j
    change tensorCoefficients e (TensorProduct.map LinearMap.id ψ t) j = _
    rw [tensorCoefficients_map, ht j]
    simp

/-- A coefficient map kills a tensor precisely when it kills its coefficient subspace. -/
lemma tensor_map_eq_zero_iff_subspace (ψ : V →ₗ[K] V') (t : H ⊗[K] V) :
    TensorProduct.map LinearMap.id ψ t = 0 ↔ tensorCoefficientSubspace e t ≤ ψ.ker := by
  rw [tensor_map_eq_zero_iff_coefficients e, tensorCoefficientSubspace, Submodule.span_le]
  constructor
  · rintro h _ ⟨j, rfl⟩
    exact h j
  · intro h j
    exact h ⟨j, rfl⟩

/-- The coefficient subspace has dimension at most the cohomology factor. -/
lemma tensorCoefficientSubspace_finrank_le (t : H ⊗[K] V) :
    Module.finrank K (tensorCoefficientSubspace e t) ≤ Module.finrank K H := by
  let := Fintype.ofFinite η
  rw [Module.finrank_eq_card_basis e]
  exact finrank_range_le_card (R := K) (tensorCoefficients e t)

/-- The finite coefficient subspace is independent of the finite basis of its first factor. -/
lemma tensorCoefficientSubspace_basis_independent {η' : Type u} [Finite η']
    (e' : Module.Basis η' K H) (t : H ⊗[K] V) :
    tensorCoefficientSubspace e t = tensorCoefficientSubspace e' t := by
  apply le_antisymm
  · have h := (tensor_map_eq_zero_iff_subspace e'
      (tensorCoefficientSubspace e' t).mkQ t).mpr (by simp)
    have h' := (tensor_map_eq_zero_iff_subspace e
      (tensorCoefficientSubspace e' t).mkQ t).mp h
    simpa only [Submodule.ker_mkQ] using h'
  · have h := (tensor_map_eq_zero_iff_subspace e
      (tensorCoefficientSubspace e t).mkQ t).mpr (by simp)
    have h' := (tensor_map_eq_zero_iff_subspace e'
      (tensorCoefficientSubspace e t).mkQ t).mp h
    simpa only [Submodule.ker_mkQ] using h'

end TensorCoefficients

/-- Proper coherent cohomology makes each actual residue-fibre structure
cohomology space finite dimensional. -/
lemma residueCohomology_finite {k K : Type u} [CommRing k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (n : ℕ) :
    Module.Finite K (ResidueCohomology (K := K) f n) := by
  let Y := (relativeSpace f).obj (ArtinianTest.residueBase k K)
  let pK := (relativeProjection f).app (ArtinianTest.residueBase k K)
  let O := SheafOfModules.unit Y.ringCatSheaf
  let : IsProper pK := inferInstanceAs
    (IsProper (Limits.pullback.fst (ArtinianTest.residueBase k K).hom f))
  let : O.IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit Y
  exact (Langlands.AlgebraicGeometry.Modules.properCoherentCohomologyFinite K Y pK
    inferInstance O inferInstance (by
      intro U
      change Module.Finite Γ(Y, U.1) Γ(Y, U.1)
      infer_instance)).1 n

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)] [Flat f] [IsProper f]

local notation "hq" => he.out
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq

variable {ι η : Type u} [Finite ι] [Finite η]
  (b : Module.Basis ι K (Kernel q)) (n : ℕ)
  (e : Module.Basis η K (ResidueCohomology (K := K) f n))

/-- The actual coefficient subspace of a class under its existing ideal tensor comparison. -/
def cohomologyCoefficientSubspace (x : Cohomology f q n) : Submodule K (Kernel q) := by
  letI := ArtinianPicardObstructionFinite.residueModule f q hq n
  exact tensorCoefficientSubspace e (idealCohomologyTensorEquiv f q b n x)

/-- The actual coefficient subspace is bounded by residue-fibre cohomology dimension. -/
lemma cohomologyCoefficientSubspace_finrank_le (x : Cohomology f q n) :
    Module.finrank K (cohomologyCoefficientSubspace f q b n e x) ≤
      Module.finrank K (ResidueCohomology (K := K) f n) := by
  let := ArtinianPicardObstructionFinite.residueModule f q hq n
  exact tensorCoefficientSubspace_finrank_le e (idealCohomologyTensorEquiv f q b n x)

variable (W : Submodule K (Kernel q))
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

/-- The actual ideal cohomology quotient kills a class exactly when the quotient
subspace contains its actual coefficient subspace. -/
lemma cohomology_quotient_eq_zero_iff (x : Cohomology f q n) :
    cohomologySemilinearMap f q W n x = 0 ↔
      cohomologyCoefficientSubspace f q b n e x ≤ W := by
  let := ArtinianPicardObstructionFinite.residueModule f q hq n
  let := ArtinianPicardObstructionFinite.residueModule f r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n
  let : FiniteDimensional K (Kernel r) :=
    ElementaryKernel.finiteDimensional r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W)
  let c := Module.Free.chooseBasis K (Kernel r)
  have ht := idealCohomologyTensorEquiv_quotient f q W b c n x
  have hz : cohomologySemilinearMap f q W n x = 0 ↔
      residueCohomologyTensorQuotientMap f q W n
        (idealCohomologyTensorEquiv f q b n x) = 0 := by
    rw [← ht]
    exact (idealCohomologyTensorEquiv f r c n).map_eq_zero_iff.symm
  rw [hz]
  change TensorProduct.map LinearMap.id
      (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)
      (idealCohomologyTensorEquiv f q b n x) = 0 ↔ _
  rw [tensor_map_eq_zero_iff_subspace e, ElementaryKernelSubspaceQuotient.ker_kernelLinearMap]
  rfl

/-- Quotienting by the coefficient subspace itself kills the actual class. -/
lemma cohomology_quotient_coefficientSubspace (x : Cohomology f q n) :
    cohomologySemilinearMap f q (cohomologyCoefficientSubspace f q b n e x) n x = 0 :=
  (cohomology_quotient_eq_zero_iff f q b n e
    (cohomologyCoefficientSubspace f q b n e x) x).mpr le_rfl

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomologySupport
