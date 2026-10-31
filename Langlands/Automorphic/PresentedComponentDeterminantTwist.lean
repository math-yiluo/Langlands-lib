import Langlands.Automorphic.PresentedLocalComponent
import Langlands.Automorphic.FiniteLocalDeterminantTwist

/-! # Actual determinant images of presented local components -/

noncomputable section
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance componentTwistRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance componentTwistContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance componentTwistSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance componentTwistFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

private theorem scalarCovariance_exists_fixed
    {G : Type*} [Group G] {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρA : Representation ℂ G A) (ρB : Representation ℂ G B)
    (η : G →* ℂˣ) (q : A ≃ₗ[ℂ] B)
    (hq : ∀ g x, ρB g (q x) = (η g : ℂ) • q (ρA g x))
    (K : Set G) (hη : ∀ g ∈ K, η g = 1)
    (hfixed : ∃ x : A, x ≠ 0 ∧ ∀ g ∈ K, ρA g x = x) :
    ∃ y : B, y ≠ 0 ∧ ∀ g ∈ K, ρB g y = y := by
  obtain ⟨x, hx, hfixed⟩ := hfixed
  refine ⟨q x, ?_, ?_⟩
  · intro hz
    exact hx (q.injective (hz.trans q.map_zero.symm))
  · intro g hg
    rw [hq, hfixed g hg, hη g hg, Units.val_one, one_smul]

namespace FiniteTensorPresentation

variable (P : FiniteTensorPresentation F n ρ E e he S)
variable (hS : S.IsNonzero F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

/-- Multiply the existing actual local slice, retaining its chosen nonzero tail. -/
def determinantTwistLocalComponent (v : FinitePlace F) : LocalRealization F n v :=
  (P.localComponent hS v).determinantTwist χ hχ

theorem determinantTwistLocalComponent_ne_bot (v : FinitePlace F) :
    P.determinantTwistLocalComponent hS χ hχ v ≠ ⊥ :=
  ((P.localComponent hS v).determinantTwist_ne_bot_iff χ hχ).mpr
    (P.localComponent_ne_bot hS v)

/-- This local copy lies inside the whole local restriction of the multiplied
finite adelic realization. -/
theorem determinantTwistLocalComponent_le (v : FinitePlace F) :
    P.determinantTwistLocalComponent hS χ hχ v ≤
      (S.determinantTwist χ hχ).toLocal F n v := by
  rw [FiniteRealization.toLocal_determinantTwist]
  exact LocalRealization.determinantTwist_mono _ χ hχ (P.localComponent_le hS v)

/-- The source is the existing scalar twist of the specified local factor. -/
def determinantTwistLocalComponentEquiv (v : FinitePlace F) :
    (Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom (ρ v)).Equiv
      (P.determinantTwistLocalComponent hS χ hχ v).representation :=
  (Langlands.twistEquiv (χ.finiteLocalDeterminant n v).toMonoidHom
    (P.localComponentEquiv hS v)).trans
    ((P.localComponent hS v).determinantTwistRepresentationEquiv χ hχ)

@[simp]
theorem determinantTwistLocalComponentEquiv_apply (v : FinitePlace F) (x : V v) :
    P.determinantTwistLocalComponentEquiv hS χ hχ v x =
      (P.localComponent hS v).determinantTwistEquiv χ hχ
        (P.localComponentEquiv hS v x) := rfl

@[simp]
theorem evaluate_determinantTwistLocalComponentEquiv
    (v : FinitePlace F) (x : V v) (a : AdelicGL F n) :
    evaluate F n ((P.determinantTwistLocalComponent hS χ hχ v).toContinuous
      (P.determinantTwistLocalComponentEquiv hS χ hχ v x)) a =
      (χ.adelicDeterminant n a : ℂ) *
        evaluate F n ((P.localComponent hS v).toContinuous
          (P.localComponentEquiv hS v x)) a := rfl

include P hS hχ in
/-- Smoothness of the twisted specified factor follows from its faithful
occurrence in the actual multiplied local form subspace. -/
theorem determinantTwistLocalFactor_isSmooth (v : FinitePlace F) :
    Langlands.IsSmooth
      (Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom (ρ v)) :=
  Langlands.isSmooth_of_injective
    (P.determinantTwistLocalComponentEquiv hS χ hχ v).toIntertwiningMap
    (P.determinantTwistLocalComponentEquiv hS χ hχ v).injective
    (P.determinantTwistLocalComponent hS χ hχ v).isSmooth

/-- The actual representative lies in the universe of forms. -/
def determinantTwistLocalComponentClass (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  (P.determinantTwistLocalComponent hS χ hχ v).isoClass

/-- Presentations with the same local tensor data produce the same twisted
component class, even inside different actual finite realizations. -/
theorem determinantTwistLocalComponentClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (hS' : S'.IsNonzero F n) (v : FinitePlace F) :
    P.determinantTwistLocalComponentClass hS χ hχ v =
      Q.determinantTwistLocalComponentClass hS' χ hχ v :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨(P.determinantTwistLocalComponentEquiv hS χ hχ v).symm.trans
      (Q.determinantTwistLocalComponentEquiv hS' χ hχ v)⟩

/-- Triviality of the actual local determinant character on the integral
subgroup preserves a nonzero integral-fixed vector. -/
theorem determinantTwistLocalComponent_exists_integral_fixed
    (v : FinitePlace F) (hv : v ∉ E)
    (hlocal : ∀ g ∈ localIntegral F n v, χ.finiteLocalDeterminant n v g = 1) :
    ∃ f : (P.determinantTwistLocalComponent hS χ hχ v).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n v,
        (P.determinantTwistLocalComponent hS χ hχ v).representation g f = f := by
  exact scalarCovariance_exists_fixed
    (P.localComponent hS v).representation
    ((P.localComponent hS v).determinantTwist χ hχ).representation
    (χ.finiteLocalDeterminant n v).toMonoidHom
    ((P.localComponent hS v).determinantTwistEquiv χ hχ).toLinearEquiv
    ((P.localComponent hS v).determinantTwistEquiv_representation χ hχ)
    (localIntegral F n v) hlocal
    (P.localComponent_exists_integral_fixed hS v hv)

end FiniteTensorPresentation
end Langlands.Automorphic
