import Langlands.Global.FiniteAdelicGL.TensorTransport
import Langlands.Automorphic.FiniteLocalCMTransport
import Langlands.Automorphic.TensorPresentation

/-! # Genuine finite tensor presentations of actual CM images -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] [NumberField.IsCMField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorCMRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorCMContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCMSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCMFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

private theorem tensorCMFinite_involutive :
    Function.Involutive (CMConjugation.finiteConj F n) := by
  have hc : (CMConjugation.fieldConj F).trans (CMConjugation.fieldConj F) =
      RingEquiv.refl F := by
    apply RingEquiv.ext
    exact NumberField.IsCMField.complexConj_apply_apply F
  have h := AdelicGLTransport.finiteEquiv_trans n
    (CMConjugation.fieldConj F) (CMConjugation.fieldConj F)
  rw [hc, AdelicGLTransport.finiteEquiv_refl,
    AdelicGLTransport.finiteEquiv_complexConj] at h
  intro g
  exact (DFunLike.congr_fun h g).symm

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

/-- Factors at v use the original model at the pulled-back place and the inverse
actual completion-group map. Complex values are unchanged. -/
def complexConjFactors :
    ∀ v, Representation ℂ (FiniteLocalGL F n v)
      (V (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v)) :=
  transportFactors (CMConjugation.fieldConj F) ρ

/-- Exactly the image of the original exceptional places under the inverse place map. -/
def complexConjExceptional : Finset (FinitePlace F) :=
  transportExceptional (CMConjugation.fieldConj F) E

include he in
theorem complexConjReference_fixed
    (v : FinitePlace F) (hv : v ∉ complexConjExceptional (E := E))
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    complexConjFactors (ρ := ρ) v g
        (e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v)) =
      e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v) :=
  transportReference_fixed (CMConjugation.fieldConj F) ρ E e he v hv g hg

variable (P : FiniteTensorPresentation F n ρ E e he S)

/-- Rebase the actual arithmetic tensor equivalence using involutivity, so both
representations act by the new finite adelic group. -/
def complexConjTensorEquiv :
    Representation.Equiv
      (tensorRepresentation F n (complexConjFactors (ρ := ρ))
        (complexConjExceptional (E := E))
        (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
        (complexConjReference_fixed (he := he)))
      ((tensorRepresentation F n ρ E e he).comp
        (CMConjugation.finiteConj F n).toMonoidHom) :=
  Representation.Equiv.mk
    (tensorTransportEquiv (CMConjugation.fieldConj F) ρ E e he
      P.reference_nonzero).toLinearEquiv
    (fun g => by
      apply LinearMap.ext
      intro x
      have h := congrArg (fun f : _ →ₗ[ℂ] _ => f x)
        ((tensorTransportEquiv (CMConjugation.fieldConj F) ρ E e he
          P.reference_nonzero).isIntertwining' (CMConjugation.finiteConj F n g))
      change tensorTransportEquiv (CMConjugation.fieldConj F) ρ E e he
        P.reference_nonzero (tensorRepresentation F n (complexConjFactors (ρ := ρ))
        (complexConjExceptional (E := E))
        (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
        (complexConjReference_fixed (he := he))
        (AdelicGLTransport.finiteEquiv n (CMConjugation.fieldConj F)
          (CMConjugation.finiteConj F n g)) x) = _ at h
      have hg : AdelicGLTransport.finiteEquiv n (CMConjugation.fieldConj F)
          (CMConjugation.finiteConj F n g) = g := by
        rw [AdelicGLTransport.finiteEquiv_complexConj]
        exact tensorCMFinite_involutive g
      rw [hg] at h
      exact h)

/-- The tensor of the transported local factors is genuinely equivalent to the
actual CM image of the specified embedded finite form space. -/
def complexConjEquiv :
    Representation.Equiv
      (tensorRepresentation F n (complexConjFactors (ρ := ρ))
        (complexConjExceptional (E := E))
        (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
        (complexConjReference_fixed (he := he)))
      S.complexConj.representation :=
  P.complexConjTensorEquiv.trans
    ((Representation.Equiv.mk P.equiv.toLinearEquiv
      (fun g => P.equiv.isIntertwining' (CMConjugation.finiteConj F n g))).trans
        S.complexConjRepresentationEquiv)

@[simp]
theorem complexConjEquiv_apply
    (x : Space ℂ
      (fun v => V (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
      (complexConjExceptional (E := E))
      (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))) :
    P.complexConjEquiv x =
      S.complexConjEquiv (P.equiv (P.complexConjTensorEquiv x)) := rfl

@[simp]
theorem evaluate_complexConjEquiv
    (x : Space ℂ
      (fun v => V (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
      (complexConjExceptional (E := E))
      (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v)))
    (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      (S.complexConj.toContinuous (P.complexConjEquiv x)) a =
      ContinuousRationalFunctions.evaluate F n
        (S.toContinuous (P.equiv (P.complexConjTensorEquiv x)))
        (CMConjugation.adelicConj F n a) :=
  S.evaluate_complexConjEquiv _ a

/-- A genuine presentation of the actual CM image, with reindexed reference
vectors and exactly transported exceptions. -/
def complexConj :
    FiniteTensorPresentation F n (complexConjFactors (ρ := ρ))
      (complexConjExceptional (E := E))
      (fun v => e (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj F) v))
      (complexConjReference_fixed (he := he)) S.complexConj where
  reference_nonzero v hv := P.reference_nonzero _ (by
    simpa only [complexConjExceptional, transportExceptional,
      Finset.mem_map_equiv, Equiv.symm_symm] using hv)
  equiv := P.complexConjEquiv

end FiniteTensorPresentation
end Langlands.Automorphic
