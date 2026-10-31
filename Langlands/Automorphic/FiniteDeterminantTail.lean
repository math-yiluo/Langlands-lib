import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Representation.RestrictedTensor.Twist

/-! # Actual full integral tails for finite-order determinant characters -/

noncomputable section
open scoped Classical
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

open Langlands.RestrictedTensor Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F] (n : ℕ)

/-- Pull the actual finite determinant character across the established restricted-product equivalence. -/
def finiteRestrictedDeterminant (χ : HeckeCharacter F) :
    LocalRestrictedProduct F n →ₜ* ℂˣ :=
  ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).comp
    { toMonoidHom := (restrictedProductEquiv F n).symm.toMonoidHom
      continuous_toFun := (restrictedProductEquiv F n).symm.continuous }

@[simp]
theorem finiteRestrictedDeterminant_apply (χ : HeckeCharacter F)
    (g : FiniteAdelicGL F n) :
    χ.finiteRestrictedDeterminant n (restrictedProductEquiv F n g) =
      χ.adelicDeterminant n (AdelicGL.ofFinite F n g) := by
  change χ.adelicDeterminant n
    (AdelicGL.ofFinite F n ((restrictedProductEquiv F n).symm
      (restrictedProductEquiv F n g))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- The generic singleton restriction is the already defined actual local determinant character. -/
@[simp]
theorem localCharacter_finiteRestrictedDeterminant (χ : HeckeCharacter F)
    (v : FinitePlace F) :
    localCharacter (fun w => (localIntegral F n w).toSubgroup)
      (χ.finiteRestrictedDeterminant n).toMonoidHom v =
      (χ.finiteLocalDeterminant n v).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change χ.adelicDeterminant n (AdelicGL.ofFinite F n
    ((restrictedProductEquiv F n).symm
      (RestrictedProduct.mulSingle (fun w => localIntegral F n w) v g))) = _
  rw [restrictedProductEquiv_symm_mulSingle]
  rfl

/-- Finite order supplies an actual full integral tail on which the determinant character is one. -/
theorem exists_finiteDeterminantTail (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    ∃ E : Finset (FinitePlace F),
      ∀ t ∈ tailReferenceSubgroup (fun v => (localIntegral F n v).toSubgroup) E,
        χ.finiteRestrictedDeterminant n t = 1 := by
  apply exists_character_tail (fun v => (localIntegral F n v).toSubgroup)
    (fun v => (localIntegral F n v).isOpen)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
  exact hχ.isLocallyConstant_pullback
    ((ideleClassMap F).continuous.comp
      ((AdelicGL.determinant F n).continuous.comp
        ((AdelicGL.ofFinite F n).continuous.comp
          (restrictedProductEquiv F n).symm.continuous)))

/-- A chosen finite bound for full-tail triviality; no minimal conductor is asserted. -/
def finiteDeterminantTail (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Finset (FinitePlace F) :=
  (χ.exists_finiteDeterminantTail n hχ).choose

theorem finiteDeterminantTail_trivial (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (t : LocalRestrictedProduct F n)
    (ht : t ∈ tailReferenceSubgroup (fun v => (localIntegral F n v).toSubgroup)
      (χ.finiteDeterminantTail n hχ)) :
    χ.finiteRestrictedDeterminant n t = 1 :=
  (χ.exists_finiteDeterminantTail n hχ).choose_spec t ht

/-- Outside the chosen finite set the actual local character is trivial on the integral subgroup. -/
theorem finiteLocalDeterminant_eq_one_outside_tail
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (v : FinitePlace F) (hv : v ∉ χ.finiteDeterminantTail n hχ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    χ.finiteLocalDeterminant n v g = 1 := by
  have h := localCharacter_eq_one_of_tail
    (fun w => (localIntegral F n w).toSubgroup)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
    (χ.finiteDeterminantTail n hχ) (χ.finiteDeterminantTail_trivial n hχ) v hv g hg
  rw [localCharacter_finiteRestrictedDeterminant] at h
  exact h

/-- The actual finite determinant is the product of its local values on every adequate finite stage. -/
theorem finiteDeterminant_eq_prod (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (S : Finset (FinitePlace F)) (hS : χ.finiteDeterminantTail n hχ ⊆ S)
    (g : FiniteAdelicGL F n)
    (hg : ∀ v ∉ S, localProjection F n v g ∈ localIntegral F n v) :
    χ.adelicDeterminant n (AdelicGL.ofFinite F n g) =
      ∏ v ∈ S, χ.finiteLocalDeterminant n v (localProjection F n v g) := by
  have h := character_eq_prod_of_tail
    (fun v => (localIntegral F n v).toSubgroup)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
    (χ.finiteDeterminantTail n hχ) (χ.finiteDeterminantTail_trivial n hχ)
    S hS (restrictedProductEquiv F n g) hg
  calc
    χ.adelicDeterminant n (AdelicGL.ofFinite F n g) =
        (χ.finiteRestrictedDeterminant n).toMonoidHom
          (restrictedProductEquiv F n g) :=
      (χ.finiteRestrictedDeterminant_apply n g).symm
    _ = _ := h
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      rw [localCharacter_finiteRestrictedDeterminant]
      rfl

end Langlands.Global.HeckeCharacter
