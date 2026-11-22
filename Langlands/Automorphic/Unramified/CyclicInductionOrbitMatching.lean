import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof
import Langlands.Automorphic.LocalDeterminantTwist
import Langlands.Automorphic.Unramified.CyclicInductionSupercuspidalReduction
import Langlands.Global.Arithmetic.CyclicFiniteLocalNormKernel
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # The local data in unique-place automorphic induction matching -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open CuspidalOperatorRealization HarmonicAnalysis
open ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open scoped NumberField FiniteExtension

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local instance orbitMatchingRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance orbitMatchingContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance orbitMatchingSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance orbitMatchingFormAddCommGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance orbitMatchingLocalAddCommGroup {v : FinitePlace K} (A : LocalRealization K n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- The orbit-lift part of the strong comparison at the distinguished finite
place, with the unitary weak induction and its global norm-kernel self-twist. -/
def CyclicInductionOrbitMatchingAtUniquePlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v) (hw : ∀ w' : FinitePlacesAbove E v, w' = w)
      (r m : ℕ) (T : CuspidalOperatorRealization E m)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      r + 1 = (m + 1) * Module.finrank F E →
      HasUnitaryCentralCharacter T →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      ∃ (U : CuspidalOperatorRealization F r) (Q : CuspidalSpectralPresentation.{uF, uV} U)
        (χ : HeckeCharacter F),
        HasUnitaryCentralCharacter U ∧
        U.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass ∧
        χ.HasNormKernel E ∧ U.isoClass.IsFiniteOrderDeterminantTwist χ U.isoClass ∧
        (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible ∧
        let : w.1.asIdeal.LiesOver v.asIdeal := w.2
        let := FiniteCompletion.valuativeRel v
        let := FiniteCompletion.valuativeRel w.1
        have := FiniteCompletion.isNonarchimedeanLocalField v
        have := FiniteCompletion.isNonarchimedeanLocalField w.1
        BaseChange.HasSigmaOrbitProductLift (uniquePlaceCompletionAutEquiv w hw σ)
          (Module.finrank F E) (Q.localComponent v).representation (P.localComponent w.1).representation

/-- The orbit comparison supplies the full local induction matching condition. -/
def CyclicInductionOrbitMatchingReductionStatement : Prop :=
  CyclicInductionOrbitMatchingAtUniquePlaceStatement.{uF, uE, uV, uW} →
  CyclicInductionMatchingAtUniquePlaceStatement.{uF, uE, uV, uW}

set_option maxHeartbeats 1000000 in
theorem cyclicInductionMatching_of_orbitMatching :
    CyclicInductionOrbitMatchingReductionStatement.{uF, uE, uV, uW} := by
  intro hOrbit F E _ _ _ _ _ _ _ _ hPrime σ hgen v w hw r m T P hRank hT hP hreg
  obtain ⟨U, Q, χ, hU, hWeak, hχ, hSelf, hQI, hQA, hLift⟩ :=
    hOrbit F E hPrime σ hgen v w hw r m T P hRank hT hP hreg
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  let := FiniteCompletion.valuativeRel v
  let := FiniteCompletion.valuativeRel w.1
  have := FiniteCompletion.isNonarchimedeanLocalField v
  have := FiniteCompletion.isNonarchimedeanLocalField w.1
  let : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, eq_top_iff.mpr (fun τ _ => hgen τ)⟩
  have hKernel := HeckeCharacter.finiteComponent_ker_eq_localNorm v w.1 hχ
  obtain ⟨e⟩ :=
    Q.nonempty_localComponent_equiv_of_finiteOrderDeterminantTwist Q v χ hSelf hQI hQI
  obtain ⟨hPI, hPA, _⟩ := hP
  have hGenQ := Q.exists_generic_at_completion hU v hQI hQA
  have hGenP := P.exists_generic_at_completion hT w.1 hPI hPA
  have hUniQ := cuspidalUnitaryLocalUnitarity F r U hU Q v hQI hQA
  have hUniP := cuspidalUnitaryLocalUnitarity E m T hT P w.1 hPI hPA
  exact ⟨U, Q, hWeak, hQA.1, hUniQ, hGenQ, hPA.1, hUniP, hGenP,
    ⟨(χ.finiteComponent v).toMonoidHom, (χ.finiteComponent v).continuous, hKernel, ⟨e.symm⟩⟩,
    hLift⟩

end Langlands.Automorphic.Unramified
