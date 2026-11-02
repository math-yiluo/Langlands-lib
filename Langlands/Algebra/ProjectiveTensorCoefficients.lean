import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.Maps

/-! # Coefficient ideals for a projective tensor factor -/

noncomputable section

universe uR uP uM uN uA uB

open scoped TensorProduct

namespace Langlands.Algebra.ProjectiveTensorCoefficients

section Modules

variable {R : Type uR} [CommRing R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- Contract the right tensor factor against a linear form. -/
def contract (φ : P →ₗ[R] R) : M ⊗[R] P →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap.comp (φ.lTensor M)

@[simp]
theorem contract_tmul (φ : P →ₗ[R] R) (m : M) (p : P) :
    contract φ (m ⊗ₜ[R] p) = φ p • m := by
  simp [contract]

/-- Contraction commutes with every linear map on the left factor. -/
@[simp]
theorem contract_rTensor (φ : P →ₗ[R] R) (f : M →ₗ[R] N) (x : M ⊗[R] P) :
    contract φ (f.rTensor P x) = f (contract φ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => simp
  | add x y hx hy => simp [hx, hy]

/-- Naturality in the contracted tensor factor. -/
@[simp]
theorem contract_lTensor {Q : Type*} [AddCommGroup Q] [Module R Q]
    (φ : Q →ₗ[R] R) (s : P →ₗ[R] Q) (x : M ⊗[R] P) :
    contract φ (s.lTensor M x) = contract (φ.comp s) x := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => simp
  | add x y hx hy => simp [hx, hy]

/-- Dual contractions separate tensors with a projective right factor. No
flatness or projectivity of the left factor is required. -/
theorem eq_zero_iff_contract [Module.Projective R P] (x : M ⊗[R] P) :
    x = 0 ↔ ∀ φ : P →ₗ[R] R, contract φ x = 0 := by
  constructor
  · rintro rfl φ
    exact map_zero _
  · intro hx
    classical
    obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R P)
    have hz : s.lTensor M x = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisRight
        (Finsupp.basisSingleOne : Module.Basis P R (P →₀ R))).injective
      ext p
      rw [TensorProduct.equivFinsuppOfBasisRight_apply]
      change contract (Finsupp.basisSingleOne.coord p) (s.lTensor M x) = 0
      rw [contract_lTensor]
      exact hx _
    have hr := congrArg ((Finsupp.linearCombination R id).lTensor M) hz
    rw [← LinearMap.lTensor_comp_apply, hs] at hr
    simpa using hr

end Modules

section Algebras

variable {R : Type uR} [CommRing R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {A : Type uA} [CommRing A] [Algebra R A]
variable {B : Type uB} [CommRing B] [Algebra R B]

/-- All scalar coefficients of the tensors in a set, using every linear form
on the right factor. -/
def coefficients (I : Set (A ⊗[R] P)) : Set A :=
  {a | ∃ x ∈ I, ∃ φ : P →ₗ[R] R, contract φ x = a}

/-- The ideal imposing the simultaneous vanishing of the given tensors. -/
def coefficientIdeal (I : Set (A ⊗[R] P)) : Ideal A :=
  Ideal.span (coefficients I)

/-- The coefficient ideal detects tensor vanishing after every algebra map,
including maps to nonflat algebras. -/
theorem coefficientIdeal_le_ker_iff [Module.Projective R P]
    (I : Set (A ⊗[R] P)) (f : A →ₐ[R] B) :
    coefficientIdeal I ≤ RingHom.ker f.toRingHom ↔
      ∀ x ∈ I, f.toLinearMap.rTensor P x = 0 := by
  rw [coefficientIdeal, Ideal.span_le]
  constructor
  · intro h x hx
    apply (eq_zero_iff_contract _).mpr
    intro φ
    rw [contract_rTensor]
    change f.toRingHom (contract φ x) = 0
    exact (RingHom.mem_ker (f := f.toRingHom)).mp (h ⟨x, hx, φ, rfl⟩)
  · intro h a ha
    obtain ⟨x, hx, φ, rfl⟩ := ha
    apply RingHom.mem_ker.mpr
    change f.toLinearMap (contract φ x) = 0
    rw [← contract_rTensor, h x hx, map_zero]

/-- Coefficient ideals commute with arbitrary maps on the coefficient algebra. -/
theorem coefficientIdeal_image (I : Set (A ⊗[R] P)) (f : A →ₐ[R] B) :
    coefficientIdeal (f.toLinearMap.rTensor P '' I) =
      (coefficientIdeal I).map f.toRingHom := by
  have hcoeff : coefficients (f.toLinearMap.rTensor P '' I) =
      f.toRingHom '' coefficients I := by
    ext b
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, φ, rfl⟩
      exact ⟨contract φ x, ⟨x, hx, φ, rfl⟩, (contract_rTensor φ f.toLinearMap x).symm⟩
    · rintro ⟨a, ⟨x, hx, φ, rfl⟩, rfl⟩
      exact ⟨f.toLinearMap.rTensor P x, ⟨x, hx, rfl⟩, φ,
        contract_rTensor φ f.toLinearMap x⟩
  simpa only [coefficientIdeal, Ideal.map_span] using congrArg Ideal.span hcoeff

end Algebras

end Langlands.Algebra.ProjectiveTensorCoefficients
