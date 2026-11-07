import Langlands.GroupScheme.Rational.PolynomialGaloisDescent
import Langlands.GroupScheme.Rational.GaloisIdealDescent
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Galois conjugation with permuted polynomial coordinates -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.PolynomialGalois

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (I : Type u)

/-- Conjugate coefficients and rename variables by the supplied permutation.
The scalar algebra is the ground field, so the coefficient action is retained. -/
def conjugatePermute (σ : K ≃ₐ[k] K) (e : Equiv.Perm I) :
    MvPolynomial I K →ₐ[k] MvPolynomial I K :=
  ((MvPolynomial.rename e : MvPolynomial I K →ₐ[K] MvPolynomial I K).restrictScalars k).comp
    (conjugate k K I σ)

theorem conjugatePermute_apply (σ : K ≃ₐ[k] K) (e : Equiv.Perm I)
    (p : MvPolynomial I K) :
    conjugatePermute k K I σ e p = MvPolynomial.rename e (MvPolynomial.map σ p) := rfl

@[simp]
theorem conjugatePermute_C (σ : K ≃ₐ[k] K) (e : Equiv.Perm I) (c : K) :
    conjugatePermute k K I σ e (MvPolynomial.C c) = MvPolynomial.C (σ c) := by
  simp [conjugatePermute_apply]

@[simp]
theorem conjugatePermute_X (σ : K ≃ₐ[k] K) (e : Equiv.Perm I) (i : I) :
    conjugatePermute k K I σ e (MvPolynomial.X i) = MvPolynomial.X (e i) := by
  simp [conjugatePermute_apply]

@[simp]
theorem conjugatePermute_one :
    conjugatePermute k K I 1 1 = AlgHom.id k (MvPolynomial I K) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

/-- Both coefficient automorphisms and variable permutations compose in the
usual left-action order. -/
theorem conjugatePermute_mul (σ τ : K ≃ₐ[k] K) (e d : Equiv.Perm I) :
    conjugatePermute k K I (σ * τ) (e * d) =
      (conjugatePermute k K I σ e).comp (conjugatePermute k K I τ d) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

/-- The actual polynomial action associated to a permutation action on its
coordinate indices. -/
def orbitAction (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) :
    (K ≃ₐ[k] K) →* (MvPolynomial I K →ₐ[k] MvPolynomial I K) where
  toFun σ := conjugatePermute k K I σ (ρ σ)
  map_one' := by
    change conjugatePermute k K I 1 (ρ 1) = AlgHom.id k (MvPolynomial I K)
    rw [map_one]
    exact conjugatePermute_one k K I
  map_mul' σ τ := by
    change conjugatePermute k K I (σ * τ) (ρ (σ * τ)) =
      (conjugatePermute k K I σ (ρ σ)).comp (conjugatePermute k K I τ (ρ τ))
    rw [map_mul]
    exact conjugatePermute_mul k K I σ τ (ρ σ) (ρ τ)

@[simp]
theorem orbitAction_C (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (σ : K ≃ₐ[k] K) (c : K) :
    orbitAction k K I ρ σ (MvPolynomial.C c) = MvPolynomial.C (σ c) :=
  conjugatePermute_C k K I σ (ρ σ) c

@[simp]
theorem orbitAction_X (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (σ : K ≃ₐ[k] K) (i : I) :
    orbitAction k K I ρ σ (MvPolynomial.X i) = MvPolynomial.X (ρ σ i) :=
  conjugatePermute_X k K I σ (ρ σ) i

section Kernel

variable (A : Type u) [CommRing A] [Algebra k A]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (f : K ⊗[k] A →ₐ[k] MvPolynomial I K)
    (hf : ∀ (σ : K ≃ₐ[k] K) (x : K ⊗[k] A),
      f (TensorGaloisPoint.coefficientConjugate k K A σ x) =
        orbitAction k K I ρ σ (f x))

include hf in
/-- Equivariance of the coordinate pullback makes its actual kernel ideal
stable under coefficient conjugation. -/
theorem coefficientConjugate_mem_ker (σ : K ≃ₐ[k] K) (x : K ⊗[k] A)
    (hx : x ∈ RingHom.ker f.toRingHom) :
    TensorGaloisPoint.coefficientConjugate k K A σ x ∈ RingHom.ker f.toRingHom := by
  change f (TensorGaloisPoint.coefficientConjugate k K A σ x) = 0
  rw [hf σ x]
  change f x = 0 at hx
  rw [hx, map_zero]

include hf in
/-- Over any Galois extension, the equivariant pullback kernel is exactly
extended from its contraction along the ground-algebra inclusion. -/
theorem map_groundIdeal_ker_eq [IsGalois k K] :
    (GaloisIdealDescent.groundIdeal k K A (RingHom.ker f.toRingHom)).map
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom =
      RingHom.ker f.toRingHom :=
  GaloisIdealDescent.map_groundIdeal_eq k K A (RingHom.ker f.toRingHom)
    (coefficientConjugate_mem_ker k K I A ρ f hf)

end Kernel

end Langlands.GroupScheme.PolynomialGalois
