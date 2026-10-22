import Langlands.Global.Adelic

/-!
# Hecke characters on the actual idele-class group

Characters here may be nonunitary. The unitary predicate is separate, in
agreement with the quasi-character convention used in the cited originals.
-/

noncomputable section

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- A continuous complex quasi-character of the actual idele-class group. -/
abbrev HeckeCharacter := IdeleClasses K →ₜ* ℂˣ

namespace HeckeCharacter

variable {K}

/-- Pull a Hecke character back to the full idele group. -/
def onIdeles (χ : HeckeCharacter K) : Ideles K →ₜ* ℂˣ :=
  χ.comp (ideleClassMap K)

/-- A continuous idele character trivial on every principal idele. -/
abbrev TrivialOnPrincipal :=
  {χ : Ideles K →ₜ* ℂˣ // ∀ a : Kˣ, χ (diagonalUnits K a) = 1}

/-- Descend an actual continuous idele character through the principal subgroup. -/
def ofIdeleCharacter (χ : Ideles K →ₜ* ℂˣ)
    (hχ : ∀ a : Kˣ, χ (diagonalUnits K a) = 1) : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift (principalIdeles K) χ.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact hχ a)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr χ.continuous

@[simp]
theorem onIdeles_diagonalUnits (χ : HeckeCharacter K) (a : Kˣ) :
    χ.onIdeles (diagonalUnits K a) = 1 := by
  simp [onIdeles]

@[simp]
theorem ofIdeleCharacter_class (χ : Ideles K →ₜ* ℂˣ)
    (hχ : ∀ a : Kˣ, χ (diagonalUnits K a) = 1) (a : Ideles K) :
    ofIdeleCharacter χ hχ (ideleClassMap K a) = χ a := rfl

/-- Characters of the quotient are exactly continuous idele characters trivial
on principal ideles. Both directions are actual constructions. -/
def ideleCharacterEquiv : HeckeCharacter K ≃ TrivialOnPrincipal (K := K) where
  toFun χ := ⟨χ.onIdeles, χ.onIdeles_diagonalUnits⟩
  invFun χ := ofIdeleCharacter χ.1 χ.2
  left_inv χ := by
    ext x
    refine Quotient.inductionOn x (fun a ↦ ?_)
    rfl
  right_inv χ := by
    apply Subtype.ext
    ext a
    rfl

/-- The continuous character on one finite local multiplicative group. -/
def finiteComponent (χ : HeckeCharacter K) (v : FinitePlace K) :
    (FiniteCompletion K v)ˣ →ₜ* ℂˣ :=
  χ.comp (finiteClassInclusion K v)

/-- The continuous character on one archimedean local multiplicative group. -/
def infiniteComponent (χ : HeckeCharacter K) (v : InfinitePlace K) :
    (InfiniteCompletion K v)ˣ →ₜ* ℂˣ :=
  χ.comp (infiniteClassInclusion K v)

/-- The character on the whole archimedean idele factor. -/
def atInfinity (χ : HeckeCharacter K) : (InfiniteAdeles K)ˣ →ₜ* ℂˣ :=
  χ.onIdeles.comp (infiniteIdelesInclusion K)

/-- The character on the whole finite idele factor. -/
def atFinite (χ : HeckeCharacter K) : FiniteIdeles K →ₜ* ℂˣ :=
  χ.onIdeles.comp (finiteIdelesInclusion K)

/-- Unitarity, stated on the actual complex values. -/
def IsUnitary (χ : HeckeCharacter K) : Prop :=
  ∀ a : IdeleClasses K, ‖(χ a : ℂ)‖ = 1

/-- Finite order in the group of continuous characters. -/
def HasFiniteOrder (χ : HeckeCharacter K) : Prop :=
  ∃ n : ℕ, 0 < n ∧ χ ^ n = 1

/-- Unramified at a finite place means trivial on the local integral units. -/
def IsUnramifiedAt (χ : HeckeCharacter K) (v : FinitePlace K) : Prop :=
  ∀ a : (FiniteCompletion K v)ˣ,
    a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units →
      χ.finiteComponent v a = 1

/-- Equality with prescribed characters at a finite set of finite places.
This predicate asserts no extension or existence theorem. -/
def HasPrescribedFiniteComponents (χ : HeckeCharacter K) (S : Finset (FinitePlace K))
    (η : (v : {v // v ∈ S}) → (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ) : Prop :=
  ∀ v, χ.finiteComponent v.1 = η v

/-- Equality with a prescribed continuous character of the archimedean factor. -/
def HasPrescribedInfinityComponent (χ : HeckeCharacter K)
    (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ) : Prop :=
  χ.atInfinity = η

@[simp]
theorem finiteComponent_mul (χ ψ : HeckeCharacter K) (v : FinitePlace K) :
    (χ * ψ).finiteComponent v = χ.finiteComponent v * ψ.finiteComponent v := rfl

@[simp]
theorem infiniteComponent_mul (χ ψ : HeckeCharacter K) (v : InfinitePlace K) :
    (χ * ψ).infiniteComponent v = χ.infiniteComponent v * ψ.infiniteComponent v := rfl

@[simp]
theorem finiteComponent_inv (χ : HeckeCharacter K) (v : FinitePlace K) :
    χ⁻¹.finiteComponent v = (χ.finiteComponent v)⁻¹ := rfl

@[simp]
theorem infiniteComponent_inv (χ : HeckeCharacter K) (v : InfinitePlace K) :
    χ⁻¹.infiniteComponent v = (χ.infiniteComponent v)⁻¹ := rfl

end HeckeCharacter
end Langlands.Global
