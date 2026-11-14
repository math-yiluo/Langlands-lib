import Langlands.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceStatement
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.AllField.Representation.Whittaker.ModelGenericSocleStatement
/-!
# Occurrence of the generic model socle in induction of block socles

The constituent step of JPSS (1983), Section 5.4, printed page 423,
for actual canonical normalized upper two-block induction.
This module defines a proposition and supplies no proof.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockModelGenericSocleOccurrenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding ModelGenericSocleStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- The least irreducible generic subrepresentation of the induced coefficient
model is an actual subquotient of normalized induction of the least generic
subrepresentations of the block coefficient models. The original blocks may
be reducible. The four socle clauses are those of `ModelGenericSocleStatement`.
-/
def TwoBlockModelGenericSocleOccurrenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∀ ℓ : ∀ i, glFunctionals ψ (m i) (σ i),
      (∀ i, (ℓ i).val ≠ 0) →
      letI : ∀ i, AddCommGroup (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule :=
        fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
      let I := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ
      ∀ ℓI : glFunctionals ψ t I, ℓI.val ≠ 0 →
      letI : AddCommGroup (glCoefficientModel ψ t I ℓI).toSubmodule :=
        (glCoefficientModel ψ t I ℓI).toSubmodule.addCommGroup
      ∀ (Si : ∀ i, Subrepresentation (glModelRepresentation ψ (m i) (σ i) (ℓ i)))
        (S : Subrepresentation (glModelRepresentation ψ t I ℓI)),
        (∀ i,
          Si i ≠ ⊥ ∧
          Representation.IsIrreducible (V := (Si i).toSubmodule) (Si i).toRepresentation ∧
          (∀ T : Subrepresentation (glModelRepresentation ψ (m i) (σ i) (ℓ i)),
            T ≠ ⊥ → Si i ≤ T) ∧
          IsOfWhittakerType (V := (Si i).toSubmodule) (m i)
            (standardCharacter ψ (m i)) (Si i).toRepresentation) →
        (S ≠ ⊥ ∧
          Representation.IsIrreducible (V := S.toSubmodule) S.toRepresentation ∧
          (∀ T : Subrepresentation (glModelRepresentation ψ t I ℓI), T ≠ ⊥ → S ≤ T) ∧
          IsOfWhittakerType (V := S.toSubmodule) t (standardCharacter ψ t)
            S.toRepresentation) →
        let J := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h)
          (fun i => (Si i).toRepresentation)
        ∃ A : Subrepresentation J,
          ∃ q : A.toRepresentation.IntertwiningMap S.toRepresentation,
            Function.Surjective q

end Langlands.AllField.RankinSelberg
