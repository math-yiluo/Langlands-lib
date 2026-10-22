import Langlands.Automorphic.Forms
import Langlands.Automorphic.ConstantTerm

/-! # Central characters and cuspidality on actual automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

/-- Impose a right-invariant condition on the actual functions realizing automorphic forms. -/
def automorphicRestriction (S : Subrepresentation (continuousRightAction K n)) :
    Subrepresentation (automorphicFiniteRightAction K n) where
  toSubmodule := S.toSubmodule.comap (automorphicToContinuous K n)
  apply_mem_toSubmodule d _ hf :=
    S.apply_mem_toSubmodule (AdelicGL.ofFinite K n d) hf

@[simp]
theorem mem_automorphicRestriction (S : Subrepresentation (continuousRightAction K n))
    (f : AutomorphicForms K n) :
    f ∈ automorphicRestriction K n S ↔ automorphicToContinuous K n f ∈ S := Iff.rfl

/-- The form space defined by an additional invariant ambient condition. -/
abbrev RestrictedAutomorphicForms (S : Subrepresentation (continuousRightAction K n)) :=
  (automorphicRestriction K n S).toSubmodule

/-- Finite adelic right translation on the restricted form space. -/
def restrictedAutomorphicFiniteRightAction
    (S : Subrepresentation (continuousRightAction K n)) :
    Representation ℂ (FiniteAdelicGL K n) (RestrictedAutomorphicForms K n S) :=
  (automorphicRestriction K n S).toRepresentation

theorem restrictedAutomorphicFiniteRightAction_isSmooth
    (S : Subrepresentation (continuousRightAction K n)) :
    Langlands.IsSmooth (restrictedAutomorphicFiniteRightAction K n S) := by
  intro f
  obtain ⟨L, hL⟩ := automorphicFiniteRightAction_isSmooth K n f.val
  exact ⟨L, fun l => Subtype.ext (hL l)⟩

/-- The injective equivariant inclusion into the full form space. -/
def restrictedAutomorphicInclusion (S : Subrepresentation (continuousRightAction K n)) :
    (restrictedAutomorphicFiniteRightAction K n S).IntertwiningMap
      (automorphicFiniteRightAction K n) where
  toLinearMap := (automorphicRestriction K n S).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem restrictedAutomorphicInclusion_injective
    (S : Subrepresentation (continuousRightAction K n)) :
    Function.Injective (restrictedAutomorphicInclusion K n S) := Subtype.val_injective

/-- The restricted forms retain their actual continuous-function realization. -/
def restrictedAutomorphicToContinuous (S : Subrepresentation (continuousRightAction K n)) :
    RestrictedAutomorphicForms K n S →ₗ[ℂ] ContinuousRationalFunctions K n :=
  (automorphicToContinuous K n).comp (automorphicRestriction K n S).toSubmodule.subtype

theorem restrictedAutomorphicToContinuous_injective
    (S : Subrepresentation (continuousRightAction K n)) :
    Function.Injective (restrictedAutomorphicToContinuous K n S) :=
  (automorphicToContinuous_injective K n).comp Subtype.val_injective

@[simp]
theorem restrictedAutomorphicToContinuous_finiteRightAction
    (S : Subrepresentation (continuousRightAction K n)) (d : FiniteAdelicGL K n)
    (f : RestrictedAutomorphicForms K n S) :
    restrictedAutomorphicToContinuous K n S
        (restrictedAutomorphicFiniteRightAction K n S d f) =
      finiteRightAction K n d (restrictedAutomorphicToContinuous K n S f) := rfl

@[simp]
theorem evaluate_restrictedAutomorphicFiniteRightAction
    (S : Subrepresentation (continuousRightAction K n)) (d : FiniteAdelicGL K n)
    (f : RestrictedAutomorphicForms K n S) (x : AdelicGL K n) :
    evaluate K n (restrictedAutomorphicToContinuous K n S
        (restrictedAutomorphicFiniteRightAction K n S d f)) x =
      evaluate K n (restrictedAutomorphicToContinuous K n S f)
        (x * AdelicGL.ofFinite K n d) := rfl

/-- Automorphic forms with the given continuous idele-class central character. -/
abbrev centralCharacterAutomorphicSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  automorphicRestriction K n (centralCharacterSubrepresentation K n χ)

abbrev CentralCharacterAutomorphicForms (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  RestrictedAutomorphicForms K n (centralCharacterSubrepresentation K n χ)

abbrev centralCharacterAutomorphicFiniteRightAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  restrictedAutomorphicFiniteRightAction K n (centralCharacterSubrepresentation K n χ)

@[simp]
theorem mem_centralCharacterAutomorphicSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (f : AutomorphicForms K n) :
    f ∈ centralCharacterAutomorphicSubrepresentation K n χ ↔
      ∀ (z : IdeleGroup (𝓞 K) K) (x : AdelicGL K n),
        evaluate K n (automorphicToContinuous K n f) (AdelicGL.scalar K n z * x) =
          (centralIdeleCharacter K χ z : ℂ) *
            evaluate K n (automorphicToContinuous K n f) x := Iff.rfl

section Cuspidal

variable [CompactSpace (AdeleQuotient K)]

/-- Cuspidal automorphic forms, using the actual normalized constant terms. -/
abbrev cuspidalAutomorphicSubrepresentation :=
  automorphicRestriction K n (cuspidalSubrepresentation (K := K) (n := n))

abbrev CuspidalAutomorphicForms :=
  RestrictedAutomorphicForms K n (cuspidalSubrepresentation (K := K) (n := n))

abbrev cuspidalAutomorphicFiniteRightAction :=
  restrictedAutomorphicFiniteRightAction K n
    (cuspidalSubrepresentation (K := K) (n := n))

@[simp]
theorem mem_cuspidalAutomorphicSubrepresentation (f : AutomorphicForms K n) :
    f ∈ cuspidalAutomorphicSubrepresentation K n ↔
      IsCuspidal K n (automorphicToContinuous K n f) := Iff.rfl

/-- Cuspidality and the specified central character imposed on the same actual form. -/
abbrev centralCharacterCuspidalSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  automorphicRestriction K n
    (centralCharacterSubrepresentation K n χ ⊓
      cuspidalSubrepresentation (K := K) (n := n))

abbrev CentralCharacterCuspidalForms (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  RestrictedAutomorphicForms K n
    (centralCharacterSubrepresentation K n χ ⊓
      cuspidalSubrepresentation (K := K) (n := n))

/-- The type of finite adelic representations on the specified-character cusp space. -/
abbrev CentralCharacterCuspidalFiniteAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :=
  Representation ℂ (FiniteAdelicGL K n) (CentralCharacterCuspidalForms K n χ)

abbrev centralCharacterCuspidalFiniteRightAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) : CentralCharacterCuspidalFiniteAction K n χ :=
  restrictedAutomorphicFiniteRightAction K n
    (centralCharacterSubrepresentation K n χ ⊓
      cuspidalSubrepresentation (K := K) (n := n))

@[simp]
theorem mem_centralCharacterCuspidalSubrepresentation
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (f : AutomorphicForms K n) :
    f ∈ centralCharacterCuspidalSubrepresentation K n χ ↔
      f ∈ centralCharacterAutomorphicSubrepresentation K n χ ∧
        IsCuspidal K n (automorphicToContinuous K n f) := Iff.rfl

theorem centralCharacterCuspidalSubrepresentation_eq_inf
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) :
    centralCharacterCuspidalSubrepresentation K n χ =
      centralCharacterAutomorphicSubrepresentation K n χ ⊓
        cuspidalAutomorphicSubrepresentation K n := by
  apply Subrepresentation.toSubmodule_injective
  rfl

theorem constantTerm_cuspidalAutomorphicForm {a b : ℕ} (h : a + b = n)
    (ha : 0 < a) (hb : 0 < b) (f : CuspidalAutomorphicForms K n)
    (g : AdelicGL K n) :
    constantTerm K n h (automorphicToContinuous K n f.val) g = 0 :=
  f.property a b h ha hb g

theorem constantTerm_centralCharacterCuspidalForm
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) {a b : ℕ} (h : a + b = n)
    (ha : 0 < a) (hb : 0 < b) (f : CentralCharacterCuspidalForms K n χ)
    (g : AdelicGL K n) :
    constantTerm K n h (automorphicToContinuous K n f.val) g = 0 :=
  f.property.2 a b h ha hb g

end Cuspidal

end Langlands.Automorphic
