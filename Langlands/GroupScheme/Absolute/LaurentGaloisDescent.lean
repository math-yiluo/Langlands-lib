import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.Galois.Basic

/-! # Descent of Galois-invariant Laurent coordinates -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentGaloisDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Extension of the coefficients of a Laurent polynomial. -/
def extend : LaurentPolynomial k →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapRingHom ℤ (algebraMap k K)

@[simp] theorem coeff_extend (p : LaurentPolynomial k) (m : ℤ) :
    (extend k K p).coeff m = algebraMap k K (p.coeff m) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

theorem extend_injective : Function.Injective (extend k K) :=
  AddMonoidAlgebra.map_injective _ (algebraMap k K).injective

/-- The coefficientwise action of a field automorphism on Laurent coordinates. -/
def conjugate (σ : K ≃ₐ[k] K) : LaurentPolynomial K →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom

@[simp] theorem coeff_conjugate (σ : K ≃ₐ[k] K) (p : LaurentPolynomial K) (m : ℤ) :
    (conjugate k K σ p).coeff m = σ (p.coeff m) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

@[simp] theorem conjugate_extend (σ : K ≃ₐ[k] K) (p : LaurentPolynomial k) :
    conjugate k K σ (extend k K p) = extend k K p := by
  ext m
  simp

variable [FiniteDimensional k K] [IsGalois k K]

/-- A Laurent polynomial comes from the base field exactly when it is Galois-fixed. -/
theorem mem_range_extend_iff (p : LaurentPolynomial K) :
    p ∈ Set.range (extend k K) ↔ ∀ σ : K ≃ₐ[k] K, conjugate k K σ p = p := by
  constructor
  · rintro ⟨q, rfl⟩ σ
    exact conjugate_extend k K σ q
  · intro h
    change p ∈ Set.range (AddMonoidAlgebra.map (algebraMap k K).toAddMonoidHom)
    rw [AddMonoidAlgebra.range_map]
    intro m
    apply (IsGalois.mem_range_algebraMap_iff_fixed (p.coeff m)).mpr
    intro σ
    exact congrArg (fun q : LaurentPolynomial K => q.coeff m) (h σ)

section RingHom

variable {A : Type v} [CommRing A] (f : A →+* LaurentPolynomial K)
  (hf : ∀ (σ : K ≃ₐ[k] K) (x : A), conjugate k K σ (f x) = f x)

/-- The unique polynomial over `k` extending to a specified invariant coordinate. -/
def descendValue (x : A) : LaurentPolynomial k :=
  ((mem_range_extend_iff k K (f x)).mpr (fun σ => hf σ x)).choose

@[simp] theorem extend_descendValue (x : A) :
    extend k K (descendValue k K f hf x) = f x :=
  ((mem_range_extend_iff k K (f x)).mpr (fun σ => hf σ x)).choose_spec

/-- An invariant Laurent-valued ring map descends to the base field. -/
def descendRingHom : A →+* LaurentPolynomial k where
  toFun := descendValue k K f hf
  map_one' := (extend_injective k K) (by simp)
  map_mul' x y := (extend_injective k K) (by simp)
  map_zero' := (extend_injective k K) (by simp)
  map_add' x y := (extend_injective k K) (by simp)

@[simp] theorem extend_descendRingHom (x : A) :
    extend k K (descendRingHom k K f hf x) = f x :=
  extend_descendValue k K f hf x

theorem extend_comp_descendRingHom :
    (extend k K).comp (descendRingHom k K f hf) = f := by
  apply RingHom.ext
  intro x
  exact extend_descendRingHom k K f hf x

theorem descendRingHom_unique (g : A →+* LaurentPolynomial k)
    (hg : (extend k K).comp g = f) : g = descendRingHom k K f hf := by
  apply RingHom.ext
  intro x
  apply extend_injective k K
  exact (congrArg (fun r : A →+* LaurentPolynomial K => r x) hg).trans
    (extend_descendRingHom k K f hf x).symm

include hf in
/-- Descent of an invariant Laurent-valued ring map is unique. -/
theorem existsUnique_descendRingHom :
    ∃! g : A →+* LaurentPolynomial k, (extend k K).comp g = f :=
  ⟨descendRingHom k K f hf, extend_comp_descendRingHom k K f hf,
    fun _ hg => descendRingHom_unique k K f hf _ hg⟩

end RingHom

section AlgHom

variable {A : Type v} [CommRing A] [Algebra k A] (f : A →ₐ[k] LaurentPolynomial K)
  (hf : ∀ (σ : K ≃ₐ[k] K) (x : A), conjugate k K σ (f x) = f x)

/-- The descended map retains the algebra structure over the original field. -/
def descendAlgHom : A →ₐ[k] LaurentPolynomial k where
  __ := descendRingHom k K f.toRingHom hf
  commutes' r := by
    apply extend_injective k K
    change extend k K (descendRingHom k K f.toRingHom hf (algebraMap k A r)) =
      extend k K (algebraMap k (LaurentPolynomial k) r)
    rw [extend_descendRingHom]
    change f (algebraMap k A r) =
      extend k K (algebraMap k (LaurentPolynomial k) r)
    rw [f.commutes]
    change AddMonoidAlgebra.single 0 (algebraMap k K r) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap k K) (AddMonoidAlgebra.single 0 r)
    exact (AddMonoidAlgebra.mapRingHom_single (algebraMap k K) 0 r).symm

@[simp] theorem extend_descendAlgHom (x : A) :
    extend k K (descendAlgHom k K f hf x) = f x :=
  extend_descendRingHom k K f.toRingHom hf x

end AlgHom

end Langlands.GroupScheme.LaurentGaloisDescent
