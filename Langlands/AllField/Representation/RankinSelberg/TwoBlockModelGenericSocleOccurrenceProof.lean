import Langlands.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceProof
import Langlands.AllField.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceStatement
import Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer
/-!
# Generic model socle occurrence in normalized upper induction

Induce the block coefficient quotients, and inject induction of the block
socles into that quotient. Extend a nonzero Whittaker functional from this
injected representation. Its coefficient map has nonzero image in the
specified original coefficient model, hence contains the specified least
socle. Restriction to its inverse image gives the actual subquotient.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockModelGenericSocleOccurrenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType twoBlockModelGenericSocleOccurrence
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement ModelGenericSocleStatement UnipotentOrbitStatement compactLocalization functionalsCongr inducedLocalization_of_prerequisites unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uG uX uY uZ

namespace ModelSocleOccurrence
open Langlands.RankinSelberg.ModelSocleOccurrence
open Langlands.AllField.RankinSelberg.ModelSocleOccurrence
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockModelGenericSocleOccurrenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType twoBlockModelGenericSocleOccurrence
open Langlands.AllField.RankinSelberg

end ModelSocleOccurrence

/-- The specified least generic model socle is an actual subquotient of
normalized induction of the specified block model socles. -/
theorem twoBlockModelGenericSocleOccurrence :
    TwoBlockModelGenericSocleOccurrenceStatement.{uF,uV} := by
  intro F _ _ _ _
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  intro ψ t m h V _ _ σ hσ ℓ _
  let : ∀ i, AddCommGroup (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  intro I ℓI hℓI
  let : AddCommGroup (glCoefficientModel ψ t I ℓI).toSubmodule :=
    (glCoefficientModel ψ t I ℓI).toSubmodule.addCommGroup
  intro Si S hSi hS J
  let := T.generalLinearTopologicalGroup (t + 1)
  let B := succBlockShape m h
  let W : Fin 2 → Type uF :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule
  let τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i) :=
    fun i => glModelRepresentation ψ (m i) (σ i) (ℓ i)
  let K := (⟨⟩ : LocalFieldData F).normalizedProductInduced B τ
  let q : I.IntertwiningMap K := T.normalizedProductModelMap B σ ℓ
  have hq : Function.Surjective q :=
    T.normalizedProductModelMap_surjective B σ (fun i => (hσ i).1.1) ℓ
  let incl : ∀ i, (Si i).toRepresentation.IntertwiningMap (τ i) :=
    fun i => { toLinearMap := (Si i).toSubmodule.subtype
               isIntertwining' := fun _ => rfl }
  let j : J.IntertwiningMap K := T.normalizedProductInducedMap B incl
  have htensor : Function.Injective (FiniteTensor.externalMap incl) := by
    change Function.Injective (PiTensorProduct.map (fun i => (Si i).toSubmodule.subtype))
    exact ModelSocleOccurrence.tensor_subtype_injective (X := W)
      (fun i => (Si i).toSubmodule)
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply htensor
    exact congrArg (fun z => z.1.1 g) hxy
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType F ψ t 2 m h (W := V) σ hσ
  have hJ : IsOfWhittakerType t (standardCharacter ψ t) J :=
    normalizedProductWhittakerType F ψ t 2 m h
      (W := fun i => (Si i).toSubmodule) (fun i => (Si i).toRepresentation)
      (fun i => (hSi i).2.2.2)
  have hθ : IsLocallyConstant
      (fun u : upperUnipotent (t + 1) F => (standardCharacter ψ t u : ℂ)) :=
    character_isLocallyConstant_of_hasFunctional _ _ _ hI.1.1 ⟨ℓI, hℓI⟩
  have hK : IsSmooth K := T.isSmooth_normalizedProductInduced B τ
  exact ModelSocleOccurrence.subquotient_of_common_quotient
    (upperUnipotent_isLimitOfCompactSubgroups F T (t + 1)) hθ hI hJ hK
    ℓI hℓI q hq j hj S hS.2.2.1

end Langlands.AllField.RankinSelberg
