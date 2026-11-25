import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalCompletion
import Langlands.Automorphic.Unramified.WeakInductionUnitaryCentralCharacter

/-! # Unique-place supercuspidality from strong matching of the supplied weak induction -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open CuspidalOperatorRealization
open ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open scoped NumberField FiniteExtension

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local instance suppliedOrbitRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance suppliedOrbitContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance suppliedOrbitSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance suppliedOrbitFormAddCommGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance suppliedOrbitLocalAddCommGroup {v : FinitePlace K} (A : LocalRealization K n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- Strong orbit-product comparison for given unitary cuspidal realizations:
at a unique finite place the entire orbit product of the upper action is a
sigma-lift of the actual component of the supplied weak induction. -/
def CyclicWeakInductionOrbitProductLiftAtUniquePlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v)
      (hw : ∀ w' : FinitePlacesAbove E v, w' = w)
      (r m : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E m)
      (Q : CuspidalSpectralPresentation.{uF, uV} S) (P : CuspidalSpectralPresentation.{uE, uW} T),
      HasUnitaryCentralCharacter S →
      HasUnitaryCentralCharacter T →
      (Q.localComponent v).IsIrreducible →
      (Q.localComponent v).IsAdmissible →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      S.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass →
      let : w.1.asIdeal.LiesOver v.asIdeal := w.2
      let := FiniteCompletion.valuativeRel v
      let := FiniteCompletion.valuativeRel w.1
      have := FiniteCompletion.isNonarchimedeanLocalField v
      have := FiniteCompletion.isNonarchimedeanLocalField w.1
      BaseChange.HasSigmaOrbitProductLift (uniquePlaceCompletionAutEquiv w hw σ)
        (Module.finrank F E) (Q.localComponent v).representation (P.localComponent w.1).representation

/-- The supplied-action orbit comparison and the two local sigma-lift inputs
imply the unrestricted unique-place supercuspidality target. -/
def CyclicWeakInductionSupercuspidalFromSuppliedOrbitStatement : Prop :=
  CyclicWeakInductionOrbitProductLiftAtUniquePlaceStatement.{uF, uE, uV, uW} →
  BaseChange.CuspidalSigmaLiftExistenceStatement.{uF, uE, uF, uE} →
  BaseChange.SigmaLiftGenericFibreStatement.{uF, uE, uF, uF, uE} →
  CyclicWeakInductionSupercuspidalStatement.{uF, uE, uV, uW}

set_option maxHeartbeats 1000000 in
theorem cyclicWeakInductionSupercuspidal_of_suppliedOrbit :
    CyclicWeakInductionSupercuspidalFromSuppliedOrbitStatement.{uF, uE, uV, uW} := by
  intro hMatch hExist hFibre F E _ _ _ _ _ _ _ _ hPrime σ hgen v w hw r m S T P
    hT hP hconj hWeak
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have hP' := (P.localComponent w.1).isSupercuspidal_iff_representation.mp hP
  have hreg (i : ℕ) (hi : 0 < i) (hdeg : i < Module.finrank F E) :
      ¬ T.isoClass.IsGaloisStable (σ ^ i) := by
    obtain ⟨U, R, hTU, hR, hne⟩ := hconj i hi hdeg
    exact CuspidalSpectralPresentation.not_isGaloisStable_of_localComponent_isoClass_ne
      w P R (σ ^ i) hTU hP'.1 hR.choose hne
  have hstab := CuspidalSpectralPresentation.hasTrivialGaloisStabilizer_of_distinct_conjugates
    w P hw σ hgen hP'.1 (fun i hi hdeg => by
      obtain ⟨U, R, hTU, hR, hne⟩ := hconj i hi hdeg
      exact ⟨U, R, hTU, hR.choose, hne⟩)
  have hS := weakInductionUnitaryCentralCharacter F E r m S T hT hWeak
  obtain ⟨A, hI, hA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r S
  obtain ⟨Q₀, hQ₀⟩ := S.exists_presentation_of_finiteSlice A hI hA
  have hSmall : ∃ Q : CuspidalSpectralPresentation.{uF, uV} S,
      ∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible :=
    Q₀.exists_small hQ₀
  obtain ⟨Q, hQ⟩ := hSmall
  obtain ⟨ψ, hψ⟩ := Q.exists_generic_at_completion hS v (hQ v).1 (hQ v).2
  have hOrbit := hMatch F E hPrime σ hgen v w hw r m S T Q P
    hS hT (hQ v).1 (hQ v).2 hP hreg hWeak
  have hSC := BaseChange.isSupercuspidal_of_generic_orbitProductLift_at_completion
    v w.1 hExist hFibre (uniquePlaceCompletionAutEquiv w hw σ) (Module.finrank F E)
    (isCyclicAlgebra_uniquePlace w hw σ hgen) hP'.2 hP'.1 hstab ψ hψ hOrbit
  exact ⟨S, Q, rfl, (Q.localComponent v).isSupercuspidal_iff_representation.mpr ⟨(hQ v).1, hSC⟩⟩

/-- Over a totally complex base the same comparison applies to the supplied weak induction. -/
theorem cyclicWeakInductionSupercuspidalTC_of_suppliedOrbit
    (hMatch : CyclicWeakInductionOrbitProductLiftAtUniquePlaceStatement.{uF, uE, uV, uW})
    (hExist : BaseChange.CuspidalSigmaLiftExistenceStatement.{uF, uE, uF, uE})
    (hFibre : BaseChange.SigmaLiftGenericFibreStatement.{uF, uE, uF, uF, uE}) :
    CyclicWeakInductionSupercuspidalTCStatement.{uF, uE, uV, uW} :=
  cyclicWeakInductionSupercuspidalTC_of_unrestricted
    (cyclicWeakInductionSupercuspidal_of_suppliedOrbit hMatch hExist hFibre)

end Langlands.Automorphic.Unramified
