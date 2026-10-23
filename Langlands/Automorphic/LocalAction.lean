import Langlands.Automorphic.CuspidalForms
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Actual finite local actions on automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance localActionRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance localActionContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance localActionSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance localActionFormsAddCommGroup : AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

/-- The type of actions of the actual local matrix group on all automorphic forms. -/
abbrev AutomorphicLocalAction (v : Langlands.Global.FinitePlace K) :=
  Representation ℂ (FiniteLocalGL K n v) (AutomorphicForms K n)

/-- Restrict finite adelic right translation along actual identity-supported local insertion. -/
def automorphicLocalRightAction (v : Langlands.Global.FinitePlace K) : AutomorphicLocalAction K n v :=
  (automorphicFiniteRightAction K n).comp (FiniteAdelicGL.localInclusion K n v).toMonoidHom

theorem automorphicLocalRightAction_isSmooth (v : Langlands.Global.FinitePlace K) :
    Langlands.IsSmooth (automorphicLocalRightAction K n v) :=
  Langlands.isSmooth_comp (FiniteAdelicGL.localInclusion K n v).toMonoidHom
    (FiniteAdelicGL.localInclusion K n v).continuous
    (automorphicFiniteRightAction_isSmooth K n)

@[simp]
theorem automorphicToContinuous_localRightAction (v : Langlands.Global.FinitePlace K)
    (g : FiniteLocalGL K n v) (f : AutomorphicForms K n) :
    automorphicToContinuous K n (automorphicLocalRightAction K n v g f) =
      finiteRightAction K n (FiniteAdelicGL.localInclusion K n v g)
        (automorphicToContinuous K n f) := rfl

/-- The local action is positive right translation on the actual adelic function. -/
@[simp]
theorem evaluate_automorphicLocalRightAction (v : Langlands.Global.FinitePlace K)
    (g : FiniteLocalGL K n v) (f : AutomorphicForms K n) (x : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (automorphicLocalRightAction K n v g f)) x =
      evaluate K n (automorphicToContinuous K n f)
        (x * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g)) := rfl

/-- Actions supported at two distinct places commute on the whole form space. -/
theorem automorphicLocalRightAction_commute (v w : Langlands.Global.FinitePlace K) (h : v ≠ w)
    (g : FiniteLocalGL K n v) (g' : FiniteLocalGL K n w) :
    Commute (automorphicLocalRightAction K n v g) (automorphicLocalRightAction K n w g') :=
  (FiniteAdelicGL.localInclusion_commute K n v w h g g').map
    (automorphicFiniteRightAction K n)

/-- Local fixed vectors are exactly invariant underlying adelic functions. -/
theorem mem_automorphicLocalFixedVectors (v : Langlands.Global.FinitePlace K)
    (L : Subgroup (FiniteLocalGL K n v)) (f : AutomorphicForms K n) :
    f ∈ Langlands.fixedVectors (automorphicLocalRightAction K n v) L ↔
      ∀ g : L, finiteRightAction K n (FiniteAdelicGL.localInclusion K n v g)
        (automorphicToContinuous K n f) = automorphicToContinuous K n f := by
  constructor
  · intro hf g
    exact congrArg (automorphicToContinuous K n) (hf g)
  · intro hf g
    exact automorphicToContinuous_injective K n (hf g)

/-- A global standard-integral fixed vector is integral-fixed at each finite place. -/
theorem automorphicLocalIntegral_fixed_of_standardIntegral
    (v : Langlands.Global.FinitePlace K) (f : AutomorphicForms K n)
    (hf : f ∈ Langlands.fixedVectors (automorphicFiniteRightAction K n)
      (FiniteAdelicGL.standardIntegral K n).toSubgroup) :
    f ∈ Langlands.fixedVectors (automorphicLocalRightAction K n v)
      (FiniteAdelicGL.localIntegral K n v).toSubgroup := by
  intro g
  exact hf ⟨FiniteAdelicGL.localInclusion K n v g,
    (FiniteAdelicGL.localInclusion_mem_standardIntegral K n v g).mpr g.property⟩

variable (S : Subrepresentation (continuousRightAction K n))

local instance localActionRestrictedAddCommGroup : AddCommGroup (RestrictedAutomorphicForms K n S) := Submodule.addCommGroup _

/-- The type of local actions on any invariant restriction of the actual form space. -/
abbrev RestrictedAutomorphicLocalAction (v : Langlands.Global.FinitePlace K) :=
  Representation ℂ (FiniteLocalGL K n v) (RestrictedAutomorphicForms K n S)

/-- Local right translation on an actual invariant restriction of automorphic forms. -/
def restrictedAutomorphicLocalRightAction (v : Langlands.Global.FinitePlace K) :
    RestrictedAutomorphicLocalAction K n S v :=
  (restrictedAutomorphicFiniteRightAction K n S).comp
    (FiniteAdelicGL.localInclusion K n v).toMonoidHom

theorem restrictedAutomorphicLocalRightAction_isSmooth (v : Langlands.Global.FinitePlace K) :
    Langlands.IsSmooth (restrictedAutomorphicLocalRightAction K n S v) :=
  Langlands.isSmooth_comp (FiniteAdelicGL.localInclusion K n v).toMonoidHom
    (FiniteAdelicGL.localInclusion K n v).continuous
    (restrictedAutomorphicFiniteRightAction_isSmooth K n S)

/-- The same inclusion of actual forms intertwines every local action. -/
def restrictedAutomorphicLocalInclusion (v : Langlands.Global.FinitePlace K) :
    (restrictedAutomorphicLocalRightAction K n S v).IntertwiningMap
      (automorphicLocalRightAction K n v) where
  toLinearMap := (restrictedAutomorphicInclusion K n S).toLinearMap
  isIntertwining' _ := by ext; rfl

theorem restrictedAutomorphicLocalInclusion_injective (v : Langlands.Global.FinitePlace K) :
    Function.Injective (restrictedAutomorphicLocalInclusion K n S v) :=
  restrictedAutomorphicInclusion_injective K n S

@[simp]
theorem restrictedAutomorphicToContinuous_localRightAction (v : Langlands.Global.FinitePlace K)
    (g : FiniteLocalGL K n v) (f : RestrictedAutomorphicForms K n S) :
    restrictedAutomorphicToContinuous K n S
        (restrictedAutomorphicLocalRightAction K n S v g f) =
      finiteRightAction K n (FiniteAdelicGL.localInclusion K n v g)
        (restrictedAutomorphicToContinuous K n S f) := rfl

@[simp]
theorem evaluate_restrictedAutomorphicLocalRightAction (v : Langlands.Global.FinitePlace K)
    (g : FiniteLocalGL K n v) (f : RestrictedAutomorphicForms K n S) (x : AdelicGL K n) :
    evaluate K n (restrictedAutomorphicToContinuous K n S
        (restrictedAutomorphicLocalRightAction K n S v g f)) x =
      evaluate K n (restrictedAutomorphicToContinuous K n S f)
        (x * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g)) := rfl

theorem restrictedAutomorphicLocalRightAction_commute (v w : Langlands.Global.FinitePlace K) (h : v ≠ w)
    (g : FiniteLocalGL K n v) (g' : FiniteLocalGL K n w) :
    Commute (restrictedAutomorphicLocalRightAction K n S v g)
      (restrictedAutomorphicLocalRightAction K n S w g') :=
  (FiniteAdelicGL.localInclusion_commute K n v w h g g').map
    (restrictedAutomorphicFiniteRightAction K n S)

/-- Actual local action on forms with a specified continuous idele-class character. -/
abbrev centralCharacterAutomorphicLocalRightAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (v : Langlands.Global.FinitePlace K) :=
  restrictedAutomorphicLocalRightAction K n (centralCharacterSubrepresentation K n χ) v

section Cuspidal

variable [CompactSpace (AdeleQuotient K)]

/-- Actual local action on the existing cusp-form space. -/
abbrev cuspidalAutomorphicLocalRightAction (v : Langlands.Global.FinitePlace K) :=
  restrictedAutomorphicLocalRightAction K n
    (cuspidalSubrepresentation (K := K) (n := n)) v

/-- A compact name for the local action type on cusp forms of specified character. -/
abbrev CentralCharacterCuspidalLocalAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (v : Langlands.Global.FinitePlace K) :=
  Representation ℂ (FiniteLocalGL K n v) (CentralCharacterCuspidalForms K n χ)

/-- Actual local action on cusp forms with a specified central character. -/
abbrev centralCharacterCuspidalLocalRightAction
    (χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ) (v : Langlands.Global.FinitePlace K) :
    CentralCharacterCuspidalLocalAction K n χ v :=
  restrictedAutomorphicLocalRightAction K n
    (centralCharacterSubrepresentation K n χ ⊓
      cuspidalSubrepresentation (K := K) (n := n)) v

end Cuspidal
end Langlands.Automorphic
