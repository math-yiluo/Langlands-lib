import Langlands.Automorphic.FiniteDeterminantTail
import Langlands.Global.HeckeDeterminantLocalConstancy

/-! # Full integral tails for the determinant character of any Hecke character

The finite determinant factor of an arbitrary Hecke character is locally constant
(`HeckeCharacter.isLocallyConstant_finiteDeterminant`), so it is trivial on a full integral
tail of the restricted product. These are the finite-order-free versions of the tail results
in `Langlands.Automorphic.FiniteDeterminantTail`.
-/

noncomputable section
open scoped Classical
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

open Langlands.RestrictedTensor Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F] (n : ℕ)

/-- Every Hecke character has an actual full integral tail on which the determinant character
is one. -/
theorem exists_finiteHeckeDeterminantTail (χ : HeckeCharacter F) :
    ∃ E : Finset (FinitePlace F),
      ∀ t ∈ tailReferenceSubgroup (fun v => (localIntegral F n v).toSubgroup) E,
        χ.finiteRestrictedDeterminant n t = 1 := by
  apply exists_character_tail (fun v => (localIntegral F n v).toSubgroup)
    (fun v => (localIntegral F n v).isOpen)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
  exact (χ.isLocallyConstant_finiteDeterminant n).comp_continuous
    (restrictedProductEquiv F n).symm.continuous

/-- A chosen finite bound for full-tail triviality; no minimal conductor is asserted. -/
def finiteHeckeDeterminantTail (χ : HeckeCharacter F) :
    Finset (FinitePlace F) :=
  (χ.exists_finiteHeckeDeterminantTail n).choose

theorem finiteHeckeDeterminantTail_trivial (χ : HeckeCharacter F)
    (t : LocalRestrictedProduct F n)
    (ht : t ∈ tailReferenceSubgroup (fun v => (localIntegral F n v).toSubgroup)
      (χ.finiteHeckeDeterminantTail n)) :
    χ.finiteRestrictedDeterminant n t = 1 :=
  (χ.exists_finiteHeckeDeterminantTail n).choose_spec t ht

/-- Outside the chosen finite set the actual local character is trivial on the integral subgroup. -/
theorem finiteLocalHeckeDeterminant_eq_one_outside_tail
    (χ : HeckeCharacter F)
    (v : FinitePlace F) (hv : v ∉ χ.finiteHeckeDeterminantTail n)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    χ.finiteLocalDeterminant n v g = 1 := by
  have h := localCharacter_eq_one_of_tail
    (fun w => (localIntegral F n w).toSubgroup)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
    (χ.finiteHeckeDeterminantTail n) (χ.finiteHeckeDeterminantTail_trivial n) v hv g hg
  rw [localCharacter_finiteRestrictedDeterminant] at h
  exact h

/-- The actual finite determinant is the product of its local values on every adequate finite
stage. -/
theorem finiteHeckeDeterminant_eq_prod (χ : HeckeCharacter F)
    (S : Finset (FinitePlace F)) (hS : χ.finiteHeckeDeterminantTail n ⊆ S)
    (g : FiniteAdelicGL F n)
    (hg : ∀ v ∉ S, localProjection F n v g ∈ localIntegral F n v) :
    χ.adelicDeterminant n (AdelicGL.ofFinite F n g) =
      ∏ v ∈ S, χ.finiteLocalDeterminant n v (localProjection F n v g) := by
  have h := character_eq_prod_of_tail
    (fun v => (localIntegral F n v).toSubgroup)
    (χ.finiteRestrictedDeterminant n).toMonoidHom
    (χ.finiteHeckeDeterminantTail n) (χ.finiteHeckeDeterminantTail_trivial n)
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
