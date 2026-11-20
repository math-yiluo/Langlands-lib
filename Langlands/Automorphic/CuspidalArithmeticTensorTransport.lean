import Langlands.Automorphic.CuspidalFiniteSlice
import Langlands.Automorphic.OperatorArithmeticTransport
import Langlands.Automorphic.TensorPresentation
import Langlands.Global.FiniteAdelicGL.TensorTransport
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Arithmetic transport of finite slices and their tensor presentations -/

noncomputable section

universe uK uL uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global AdelicFunctoriality AdelicGLTransport FiniteAdelicGL

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

local instance arithmeticTensorRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance arithmeticTensorContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticTensorSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticTensorFormsGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance arithmeticTensorStableGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace FiniteRealization

/-- Arithmetic pullback identifies the finite invariant subspaces of actual forms. -/
def arithmeticComapOrderIso (n : ℕ) (e : K ≃+* L) :
    FiniteRealization L n ≃o FiniteRealization K n :=
  covariantSubrepresentationOrderIso (automorphicFiniteRightAction L n)
    (automorphicFiniteRightAction K n) (finiteEquiv n e).toMulEquiv
    (AutomorphicForms.arithmeticEquiv n e).toLinearEquiv
    (fun d f => (AutomorphicForms.arithmeticEquiv_finiteRightAction n e d f).symm)

/-- Pullback onto the actual embedded image, with the finite action rebased along `e`. -/
def arithmeticComapEquiv {n : ℕ} (e : K ≃+* L) (A : FiniteRealization L n) :
    Representation.Equiv (A.representation.comp (finiteEquiv n e).toMonoidHom)
      (arithmeticComapOrderIso n e A).representation :=
  Representation.Equiv.mk
    ((AutomorphicForms.arithmeticEquiv n e).ofSubmodules _ _ rfl).toLinearEquiv
    (fun d => by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      exact AutomorphicForms.arithmeticEquiv_finiteRightAction n e d f.val)

end FiniteRealization

namespace CuspidalOperatorRealization.FiniteSlice

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
variable {r : ℕ} {S : CuspidalOperatorRealization L r}

/-- The image of a nonzero finite slice is a finite slice of the arithmetic pullback. -/
def arithmeticComap (e : K ≃+* L) (A : S.FiniteSlice) : (S.arithmeticComap e).FiniteSlice where
  subspace := FiniteRealization.arithmeticComapOrderIso (r + 1) e A.subspace
  le_image := by
    rintro f ⟨g, hg, rfl⟩
    obtain ⟨x, rfl⟩ := A.le_image hg
    refine ⟨S.realization.arithmeticComapEquiv e x, ?_⟩
    exact S.realization.formInclusion_arithmeticComapEquiv e x
  nonzero := by
    intro h
    let E := FiniteRealization.arithmeticComapOrderIso (r + 1) e
    exact A.nonzero (E.injective (h.trans E.map_bot.symm))

end CuspidalOperatorRealization.FiniteSlice

namespace FiniteTensorPresentation

variable {n : ℕ} {V : FinitePlace L → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL L n v) (V v)}
variable {E : Finset (FinitePlace L)} {z : ∀ v, V v}
variable {hz : ∀ v ∉ E, ∀ g ∈ localIntegral L n v, ρ v g (z v) = z v}
variable {A : FiniteRealization L n}

private theorem finiteEquiv_symm_apply (e : K ≃+* L) (g : FiniteAdelicGL K n) :
    finiteEquiv n e.symm (finiteEquiv n e g) = g := by
  rw [← ContinuousMulEquiv.trans_apply, ← AdelicGLTransport.finiteEquiv_trans,
    RingEquiv.self_trans_symm, AdelicGLTransport.finiteEquiv_refl]
  rfl

/-- Reindex the local factors and use the actual finite arithmetic image for the realization. -/
def arithmeticComap (e : K ≃+* L) (P : FiniteTensorPresentation L n ρ E z hz A) :
    FiniteTensorPresentation K n (transportFactors e.symm ρ)
      (transportExceptional e.symm E) (fun v => z (finitePlaceEquiv e.symm v))
      (transportReference_fixed e.symm ρ E z hz)
      (FiniteRealization.arithmeticComapOrderIso n e A) where
  reference_nonzero v hv := P.reference_nonzero _ (by
    simpa only [transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm] using hv)
  equiv := by
    let T := tensorTransportEquiv e.symm ρ E z hz P.reference_nonzero
    refine (Representation.Equiv.mk T.toLinearEquiv ?_).trans
      ((SmoothRep.pullbackEquiv (finiteEquiv n e) P.equiv).trans
        (A.arithmeticComapEquiv e))
    intro g
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (T.isIntertwining' (finiteEquiv n e g)) x
    exact (congrArg (fun k => T (tensorRepresentation K n (transportFactors e.symm ρ)
      (transportExceptional e.symm E) (fun v => z (finitePlaceEquiv e.symm v))
      (transportReference_fixed e.symm ρ E z hz) k x))
      (finiteEquiv_symm_apply e g).symm).trans h

end FiniteTensorPresentation
end Langlands.Automorphic
