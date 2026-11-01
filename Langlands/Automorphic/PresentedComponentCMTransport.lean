import Langlands.Automorphic.PresentedLocalComponent
import Langlands.Automorphic.FiniteLocalCMTransport

/-! # Actual CM images of presented local components -/

noncomputable section
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] [NumberField.IsCMField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance componentCMRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance componentCMContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance componentCMSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance componentCMFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

namespace FiniteTensorPresentation

variable (P : FiniteTensorPresentation F n ρ E e he S)
variable (hS : S.IsNonzero F n)

/-- Pull back the actual presented slice, retaining its chosen nonzero tail. -/
def complexConjLocalComponent (v : FinitePlace F) :
    LocalRealization F n
      (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v) :=
  (P.localComponent hS v).complexConj

theorem complexConjLocalComponent_ne_bot (v : FinitePlace F) :
    P.complexConjLocalComponent hS v ≠ ⊥ :=
  mt (LocalRealization.complexConj_eq_bot_iff _).mp (P.localComponent_ne_bot hS v)

/-- This actual image lies in the whole corresponding-place local restriction
of the CM image of the finite realization. -/
theorem complexConjLocalComponent_le (v : FinitePlace F) :
    P.complexConjLocalComponent hS v ≤
      S.complexConj.toLocal F n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v) := by
  rw [FiniteRealization.toLocal_complexConj]
  exact LocalRealization.complexConj_mono _ (P.localComponent_le hS v)

/-- The source is the specified local factor pulled back along the actual
isomorphism of the corresponding completion groups. -/
def complexConjLocalComponentEquiv (v : FinitePlace F) :
    Representation.Equiv
      ((ρ v).comp
        (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj F) v).toMonoidHom)
      (P.complexConjLocalComponent hS v).representation :=
  Representation.Equiv.mk
    ((P.localComponentEquiv hS v).toLinearEquiv.trans
      (P.localComponent hS v).complexConjEquiv.toLinearEquiv)
    (fun g => by
      apply LinearMap.ext
      intro x
      exact (congrArg (P.localComponent hS v).complexConjEquiv
        (LinearMap.congr_fun ((P.localComponentEquiv hS v).isIntertwining'
          (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj F) v g)) x)).trans
        ((P.localComponent hS v).complexConjEquiv_representation g
          (P.localComponentEquiv hS v x)).symm)

@[simp]
theorem complexConjLocalComponentEquiv_apply (v : FinitePlace F) (x : V v) :
    P.complexConjLocalComponentEquiv hS v x =
      (P.localComponent hS v).complexConjEquiv
        (P.localComponentEquiv hS v x) := rfl

@[simp]
theorem evaluate_complexConjLocalComponentEquiv
    (v : FinitePlace F) (x : V v) (a : AdelicGL F n) :
    evaluate F n ((P.complexConjLocalComponent hS v).toContinuous
      (P.complexConjLocalComponentEquiv hS v x)) a =
      evaluate F n ((P.localComponent hS v).toContinuous
        (P.localComponentEquiv hS v x)) (CMConjugation.adelicConj F n a) :=
  (P.localComponent hS v).evaluate_complexConjEquiv
    (P.localComponentEquiv hS v x) a

include P hS in
/-- The actual faithful form image proves smoothness of the pulled-back factor. -/
theorem complexConjLocalFactor_isSmooth (v : FinitePlace F) :
    Langlands.IsSmooth
      ((ρ v).comp
        (AdelicGLTransport.localEquiv n (CMConjugation.fieldConj F) v).toMonoidHom) :=
  Langlands.isSmooth_of_injective
    (P.complexConjLocalComponentEquiv hS v).toIntertwiningMap
    (P.complexConjLocalComponentEquiv hS v).injective
    (P.complexConjLocalComponent hS v).isSmooth

/-- Represent the transported smooth class in the universe of actual forms. -/
def complexConjLocalComponentClass (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ
      (FiniteLocalGL F n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v)) :=
  (P.complexConjLocalComponent hS v).isoClass

/-- The transported class depends only on the same specified tensor model. -/
theorem complexConjLocalComponentClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (hS' : S'.IsNonzero F n) (v : FinitePlace F) :
    P.complexConjLocalComponentClass hS v =
      Q.complexConjLocalComponentClass hS' v :=
  (LocalRealization.isoClass_eq_iff _ _).mpr
    ⟨(P.complexConjLocalComponentEquiv hS v).symm.trans
      (Q.complexConjLocalComponentEquiv hS' v)⟩

/-- The global character condition remains a condition on the embedded forms. -/
theorem complexConjLocalComponent_hasCentralCharacter (v : FinitePlace F)
    (χ : HeckeCharacter F) (hχ : S.HasCentralCharacter χ) :
    (P.complexConjLocalComponent hS v).HasCentralCharacter χ.complexConj :=
  ((P.localComponent hS v).complexConj_hasCentralCharacter_iff χ).mpr
    (P.localComponent_hasCentralCharacter hS v χ hχ)

/-- The normalized constant-term condition is inherited and transported. -/
theorem complexConjLocalComponent_isCuspidal [CompactSpace (AdeleQuotient F)]
    (v : FinitePlace F) (hC : S.IsCuspidal) :
    (P.complexConjLocalComponent hS v).IsCuspidal :=
  (LocalRealization.complexConj_isCuspidal_iff _).mpr
    (P.localComponent_isCuspidal hS v hC)

/-- Actual completion transport preserves integrality, so no character
triviality premise is needed for the transported nonzero fixed vector. -/
theorem complexConjLocalComponent_exists_integral_fixed
    (v : FinitePlace F) (hv : v ∉ E) :
    ∃ f : (P.complexConjLocalComponent hS v).Space,
      f ≠ 0 ∧ ∀ g ∈ localIntegral F n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v),
        (P.complexConjLocalComponent hS v).representation g f = f := by
  obtain ⟨f, hf, hfixed⟩ := P.localComponent_exists_integral_fixed hS v hv
  refine ⟨(P.localComponent hS v).complexConjEquiv f, ?_, ?_⟩
  · intro hz
    exact hf ((P.localComponent hS v).complexConjEquiv.injective
      (hz.trans (P.localComponent hS v).complexConjEquiv.map_zero.symm))
  · intro g hg
    exact ((P.localComponent hS v).complexConjEquiv_representation g f).trans
      (congrArg (P.localComponent hS v).complexConjEquiv
        (hfixed _ ((AdelicGLTransport.localEquiv_mem_localIntegral_iff
          n (CMConjugation.fieldConj F) v g).mpr hg)))

end FiniteTensorPresentation
end Langlands.Automorphic
