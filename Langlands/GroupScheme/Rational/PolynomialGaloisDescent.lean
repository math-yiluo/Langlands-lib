import Langlands.GroupScheme.GaloisPointDescent
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Finite-Galois descent of polynomial coefficients -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

namespace PolynomialGalois

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (I : Type u)

/-- Extend only the coefficients of a multivariate polynomial. -/
def extend : MvPolynomial I k →ₐ[k] MvPolynomial I L :=
  MvPolynomial.mapAlgHom (Algebra.ofId k L)

@[simp] theorem coeff_extend (p : MvPolynomial I k) (m : I →₀ ℕ) :
    (extend k L I p).coeff m = algebraMap k L (p.coeff m) :=
  MvPolynomial.coeff_map _ _ _

theorem extend_injective : Function.Injective (extend k L I) :=
  MvPolynomial.map_injective _ (algebraMap k L).injective

/-- Act on coefficients, keeping the polynomial variables fixed. -/
def conjugate (σ : L ≃ₐ[k] L) : MvPolynomial I L →ₐ[k] MvPolynomial I L :=
  MvPolynomial.mapAlgHom σ.toAlgHom

@[simp] theorem coeff_conjugate (σ : L ≃ₐ[k] L)
    (p : MvPolynomial I L) (m : I →₀ ℕ) :
    (conjugate k L I σ p).coeff m = σ (p.coeff m) :=
  MvPolynomial.coeff_map _ _ _

@[simp] theorem conjugate_one :
    conjugate k L I 1 = AlgHom.id k (MvPolynomial I L) := by
  apply AlgHom.ext
  intro p
  apply MvPolynomial.ext
  intro m
  simp

theorem conjugate_mul (σ τ : L ≃ₐ[k] L) :
    conjugate k L I (σ * τ) =
      (conjugate k L I σ).comp (conjugate k L I τ) := by
  apply AlgHom.ext
  intro p
  apply MvPolynomial.ext
  intro m
  simp

@[simp] theorem conjugate_extend (σ : L ≃ₐ[k] L) (p : MvPolynomial I k) :
    conjugate k L I σ (extend k L I p) = extend k L I p := by
  ext m
  simp

variable [FiniteDimensional k L] [IsGalois k L]

/-- Polynomial coordinates descend precisely when their coefficients are fixed. -/
theorem mem_range_extend_iff (p : MvPolynomial I L) :
    p ∈ Set.range (extend k L I) ↔
      ∀ σ : L ≃ₐ[k] L, conjugate k L I σ p = p := by
  constructor
  · rintro ⟨q, rfl⟩ σ
    exact conjugate_extend k L I σ q
  · intro hp
    change p ∈ Set.range (MvPolynomial.map (algebraMap k L))
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    exact congrArg (fun q : MvPolynomial I L => q.coeff m) (hp σ)

section AlgHom

variable {A : Type v} [CommRing A] [Algebra k A]
    (f : A →ₐ[k] MvPolynomial I L)
    (hf : ∀ (σ : L ≃ₐ[k] L) (a : A), conjugate k L I σ (f a) = f a)

/-- Descend one fixed polynomial coordinate. -/
def descendValue (a : A) : MvPolynomial I k :=
  ((mem_range_extend_iff k L I (f a)).mpr (fun σ => hf σ a)).choose

@[simp] theorem extend_descendValue (a : A) :
    extend k L I (descendValue k L I f hf a) = f a :=
  ((mem_range_extend_iff k L I (f a)).mpr (fun σ => hf σ a)).choose_spec

/-- A fixed polynomial-valued algebra map descends as an algebra map. -/
def descendAlgHom : A →ₐ[k] MvPolynomial I k where
  toFun := descendValue k L I f hf
  map_one' := (extend_injective k L I) (by simp)
  map_mul' a b := (extend_injective k L I) (by simp)
  map_zero' := (extend_injective k L I) (by simp)
  map_add' a b := (extend_injective k L I) (by simp)
  commutes' a := (extend_injective k L I) (by simp)

@[simp] theorem extend_descendAlgHom (a : A) :
    extend k L I (descendAlgHom k L I f hf a) = f a :=
  extend_descendValue k L I f hf a

theorem extend_comp_descendAlgHom :
    (extend k L I).comp (descendAlgHom k L I f hf) = f := by
  apply AlgHom.ext
  intro a
  exact extend_descendAlgHom k L I f hf a

theorem descendAlgHom_unique (g : A →ₐ[k] MvPolynomial I k)
    (hg : (extend k L I).comp g = f) :
    g = descendAlgHom k L I f hf := by
  apply AlgHom.ext
  intro a
  apply extend_injective k L I
  exact (DFunLike.congr_fun hg a).trans (extend_descendAlgHom k L I f hf a).symm

include hf in
/-- Descent of an invariant polynomial-valued algebra map is effective and unique. -/
theorem existsUnique_descendAlgHom :
    ∃! g : A →ₐ[k] MvPolynomial I k, (extend k L I).comp g = f :=
  ⟨descendAlgHom k L I f hf, extend_comp_descendAlgHom k L I f hf,
    fun g hg => descendAlgHom_unique k L I f hf g hg⟩

end AlgHom

end PolynomialGalois

end Langlands.GroupScheme
