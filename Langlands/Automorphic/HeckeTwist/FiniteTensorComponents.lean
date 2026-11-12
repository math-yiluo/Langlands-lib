import Langlands.Automorphic.FiniteTensorDeterminantComponents
import Langlands.Automorphic.HeckeTwist.FiniteTensorTwist
import Langlands.Automorphic.HeckeTwist.PresentedComponentTwist

/-! # Local components of the presentation twisted by any Hecke determinant character

The local components of the twisted finite tensor presentation of
`Langlands.Automorphic.HeckeTwist.FiniteTensorTwist` agree with the twisted presented local
components, and almost all of them have nonzero integral-fixed vectors. This is the
finite-order-free version of `Langlands.Automorphic.FiniteTensorDeterminantComponents`.
-/

noncomputable section
open scoped Classical
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance heckeTensorComponentTwistRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorComponentTwistContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorComponentTwistSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorComponentTwistFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}
variable (P : FiniteTensorPresentation F n ρ E e he S)
variable (hS : S.IsNonzero F n) (χ : HeckeCharacter F)

/-- Two actual local copies of the twisted factor are equivalent, even though
their auxiliary complementary vectors may differ. -/
def heckeDeterminantTwistPresentationLocalComponentEquiv (v : FinitePlace F) :
    ((P.heckeDeterminantTwist χ).localComponent
      ((S.heckeDeterminantTwist_ne_bot_iff χ).mpr hS) v).representation.Equiv
      (P.heckeDeterminantTwistLocalComponent hS χ v).representation :=
  ((P.heckeDeterminantTwist χ).localComponentEquiv
    ((S.heckeDeterminantTwist_ne_bot_iff χ).mpr hS) v).symm.trans
      (P.heckeDeterminantTwistLocalComponentEquiv hS χ v)

/-- The local class of the new global presentation agrees with the actual
determinant image of the old presented local component. -/
theorem heckeDeterminantTwistPresentationLocalComponentClass_eq (v : FinitePlace F) :
    (P.heckeDeterminantTwist χ).localComponentClass
      ((S.heckeDeterminantTwist_ne_bot_iff χ).mpr hS) v =
      P.heckeDeterminantTwistLocalComponentClass hS χ v :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨P.heckeDeterminantTwistPresentationLocalComponentEquiv hS χ v⟩

/-- The proved character tail removes the separate local-triviality hypothesis. -/
theorem heckeDeterminantTwistLocalComponent_exists_integral_fixed_outside
    (v : FinitePlace F)
    (hv : v ∉ heckeDeterminantTwistExceptional (E := E) (n := n) χ) :
    ∃ f : (P.heckeDeterminantTwistLocalComponent hS χ v).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        (P.heckeDeterminantTwistLocalComponent hS χ v).representation g f = f :=
  P.heckeDeterminantTwistLocalComponent_exists_integral_fixed hS χ v
    (fun h => hv (Finset.mem_union_left _ h))
    (fun g hg => χ.finiteLocalHeckeDeterminant_eq_one_outside_tail n v
      (fun h => hv (Finset.mem_union_right _ h)) g hg)

/-- Almost every actual multiplied local component has a nonzero integral-fixed vector. -/
theorem heckeDeterminantTwistLocalComponent_eventually_integral_fixed :
    ∀ᶠ v in Filter.cofinite,
      ∃ f : (P.heckeDeterminantTwistLocalComponent hS χ v).Space,
        f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
          (P.heckeDeterminantTwistLocalComponent hS χ v).representation g f = f :=
  (heckeDeterminantTwistExceptional (E := E) (n := n) χ).eventually_cofinite_notMem.mono
    (fun v hv => P.heckeDeterminantTwistLocalComponent_exists_integral_fixed_outside hS χ v hv)

end FiniteTensorPresentation
end Langlands.Automorphic
