import Langlands.Automorphic.FiniteTensorDeterminantTwist
import Langlands.Automorphic.PresentedComponentDeterminantTwist

/-! # Local components of the genuine determinant-twisted presentation -/

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

local instance tensorComponentTwistRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorComponentTwistContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorComponentTwistSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorComponentTwistFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}
variable (P : FiniteTensorPresentation F n ρ E e he S)
variable (hS : S.IsNonzero F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

/-- Two actual local copies of the twisted factor are equivalent, even though
their auxiliary complementary vectors may differ. -/
def determinantTwistPresentationLocalComponentEquiv (v : FinitePlace F) :
    ((P.determinantTwist χ hχ).localComponent
      ((S.determinantTwist_ne_bot_iff χ hχ).mpr hS) v).representation.Equiv
      (P.determinantTwistLocalComponent hS χ hχ v).representation :=
  ((P.determinantTwist χ hχ).localComponentEquiv
    ((S.determinantTwist_ne_bot_iff χ hχ).mpr hS) v).symm.trans
      (P.determinantTwistLocalComponentEquiv hS χ hχ v)

/-- The local class of the new global presentation agrees with the actual
determinant image of the old presented local component. -/
theorem determinantTwistPresentationLocalComponentClass_eq (v : FinitePlace F) :
    (P.determinantTwist χ hχ).localComponentClass
      ((S.determinantTwist_ne_bot_iff χ hχ).mpr hS) v =
      P.determinantTwistLocalComponentClass hS χ hχ v :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨P.determinantTwistPresentationLocalComponentEquiv hS χ hχ v⟩

/-- The proved character tail removes the separate local-triviality hypothesis. -/
theorem determinantTwistLocalComponent_exists_integral_fixed_outside
    (v : FinitePlace F)
    (hv : v ∉ determinantTwistExceptional (E := E) (n := n) χ hχ) :
    ∃ f : (P.determinantTwistLocalComponent hS χ hχ v).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        (P.determinantTwistLocalComponent hS χ hχ v).representation g f = f :=
  P.determinantTwistLocalComponent_exists_integral_fixed hS χ hχ v
    (fun h => hv (Finset.mem_union_left _ h))
    (fun g hg => χ.finiteLocalDeterminant_eq_one_outside_tail n hχ v
      (fun h => hv (Finset.mem_union_right _ h)) g hg)

/-- Almost every actual multiplied local component has a nonzero integral-fixed vector. -/
theorem determinantTwistLocalComponent_eventually_integral_fixed :
    ∀ᶠ v in Filter.cofinite,
      ∃ f : (P.determinantTwistLocalComponent hS χ hχ v).Space,
        f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
          (P.determinantTwistLocalComponent hS χ hχ v).representation g f = f :=
  (determinantTwistExceptional (E := E) (n := n) χ hχ).eventually_cofinite_notMem.mono
    (fun v hv => P.determinantTwistLocalComponent_exists_integral_fixed_outside hS χ hχ v hv)

end FiniteTensorPresentation
end Langlands.Automorphic
