import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearForms
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Linear substitution on the actual projective coordinate ring -/

noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Pull back actual coordinate polynomials along a linear endomorphism. -/
def linearSubstitution (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) :
    ProjectiveCoordinateRing R n →ₐ[R] ProjectiveCoordinateRing R n :=
  MvPolynomial.aeval fun i =>
    (linearFormPolynomialEquiv R n ((LinearMap.proj i).comp f) : ProjectiveCoordinateRing R n)

@[simp]
theorem linearSubstitution_X (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R))
    (i : Fin (n + 1)) :
    linearSubstitution R n f (MvPolynomial.X i) =
      (linearFormPolynomialEquiv R n ((LinearMap.proj i).comp f) : ProjectiveCoordinateRing R n) :=
  MvPolynomial.aeval_X _ _

@[simp]
theorem linearSubstitution_C (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R))
    (r : R) :
    linearSubstitution R n f (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [linearSubstitution]

@[simp]
theorem linearFormPolynomialEquiv_proj (i : Fin (n + 1)) :
    (linearFormPolynomialEquiv R n (LinearMap.proj i) : ProjectiveCoordinateRing R n) =
      MvPolynomial.X i := by
  classical
  simp [linearFormPolynomialEquiv_coe, Pi.single_apply]

theorem linearSubstitution_linearForm
    (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R))
    (ℓ : (Fin (n + 1) → R) →ₗ[R] R) :
    linearSubstitution R n f (linearFormPolynomialEquiv R n ℓ) =
      (linearFormPolynomialEquiv R n (ℓ.comp f) : ProjectiveCoordinateRing R n) := by
  classical
  have hℓ : (∑ i, ℓ (Pi.single i 1) • (LinearMap.proj i).comp f) = ℓ.comp f := by
    apply LinearMap.ext
    intro v
    have hv := congrArg ℓ ((Pi.basisFun R (Fin (n + 1))).sum_repr (f v))
    simpa [map_sum, map_smul, Pi.basisFun_apply, mul_comm] using hv
  rw [linearFormPolynomialEquiv_coe]
  simp only [map_sum, map_smul, linearSubstitution_X]
  have h := congrArg (fun ψ => (linearFormPolynomialEquiv R n ψ : ProjectiveCoordinateRing R n)) hℓ
  simpa only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] using h

@[simp]
theorem linearSubstitution_id : linearSubstitution R n LinearMap.id = AlgHom.id R _ := by
  ext i
  simp

/-- Pullback substitution reverses the order of composition. -/
theorem linearSubstitution_comp
    (f g : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) :
    (linearSubstitution R n f).comp (linearSubstitution R n g) =
      linearSubstitution R n (g.comp f) := by
  ext i
  simp only [AlgHom.comp_apply, linearSubstitution_X, linearSubstitution_linearForm,
    LinearMap.comp_assoc]

/-- Linear substitution preserves every actual homogeneous piece. -/
def gradedLinearSubstitution
    (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) :
    projectiveSpaceGrading R n →+*ᵍ projectiveSpaceGrading R n where
  toRingHom := (linearSubstitution R n f).toRingHom
  map_mem {i} {x} hx := by
    have hhom := (MvPolynomial.mem_homogeneousSubmodule i x).mp hx
    have h := hhom.aeval (fun j =>
      (linearFormPolynomialEquiv R n ((LinearMap.proj j).comp f) : ProjectiveCoordinateRing R n))
      (fun j => (MvPolynomial.mem_homogeneousSubmodule 1 _).mp
        (linearFormPolynomialEquiv R n ((LinearMap.proj j).comp f)).2)
    exact (MvPolynomial.mem_homogeneousSubmodule i _).mpr (by
      simpa [linearSubstitution] using h)

@[simp]
theorem gradedLinearSubstitution_apply
    (f : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) (x : ProjectiveCoordinateRing R n) :
    gradedLinearSubstitution R n f x = linearSubstitution R n f x := rfl

theorem gradedLinearSubstitution_comp
    (f g : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R)) :
    (gradedLinearSubstitution R n f).comp (gradedLinearSubstitution R n g) =
      gradedLinearSubstitution R n (g.comp f) := by
  apply GradedRingHom.ext
  intro x
  exact congrArg (fun ψ : ProjectiveCoordinateRing R n →ₐ[R] ProjectiveCoordinateRing R n => ψ x)
    (linearSubstitution_comp R n f g)

@[simp]
theorem gradedLinearSubstitution_id :
    gradedLinearSubstitution R n LinearMap.id = GradedRingHom.id (projectiveSpaceGrading R n) := by
  apply GradedRingHom.ext
  intro x
  exact congrArg (fun ψ : ProjectiveCoordinateRing R n →ₐ[R] ProjectiveCoordinateRing R n => ψ x)
    (linearSubstitution_id R n)

@[simp]
theorem linearSubstitution_symm_apply_apply
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (x : ProjectiveCoordinateRing R n) :
    linearSubstitution R n e.symm.toLinearMap (linearSubstitution R n e.toLinearMap x) = x := by
  have h := congrArg
    (fun ψ : ProjectiveCoordinateRing R n →ₐ[R] ProjectiveCoordinateRing R n => ψ x)
    (linearSubstitution_comp R n e.symm.toLinearMap e.toLinearMap)
  simpa only [AlgHom.comp_apply, LinearEquiv.comp_symm, linearSubstitution_id,
    AlgHom.id_apply] using h

@[simp]
theorem linearSubstitution_apply_symm_apply
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (x : ProjectiveCoordinateRing R n) :
    linearSubstitution R n e.toLinearMap (linearSubstitution R n e.symm.toLinearMap x) = x := by
  simpa using linearSubstitution_symm_apply_apply R n e.symm x

/-- An invertible linear change of coordinates gives an actual polynomial algebra equivalence. -/
def linearSubstitutionEquiv
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    ProjectiveCoordinateRing R n ≃ₐ[R] ProjectiveCoordinateRing R n where
  __ := linearSubstitution R n e.toLinearMap
  invFun := linearSubstitution R n e.symm.toLinearMap
  left_inv := linearSubstitution_symm_apply_apply R n e
  right_inv := linearSubstitution_apply_symm_apply R n e

/-- Invertibility supplies the irrelevant-ideal hypothesis for the actual Proj morphism. -/
theorem irrelevant_le_map_gradedLinearSubstitution
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n)).map
        (gradedLinearSubstitution R n e.toLinearMap) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi x hx
  have hx' := HomogeneousIdeal.mem_irrelevant_of_mem (projectiveSpaceGrading R n) hi
    ((gradedLinearSubstitution R n e.symm.toLinearMap).map_mem hx)
  have h := Ideal.mem_map_of_mem (gradedLinearSubstitution R n e.toLinearMap).toRingHom hx'
  change x ∈ Ideal.map (gradedLinearSubstitution R n e.toLinearMap).toRingHom
    (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n)).toIdeal
  simpa only [GradedRingHom.coe_toRingHom, gradedLinearSubstitution_apply,
    linearSubstitution_apply_symm_apply] using h

end Langlands.AlgebraicGeometry.ProjectiveSpace
