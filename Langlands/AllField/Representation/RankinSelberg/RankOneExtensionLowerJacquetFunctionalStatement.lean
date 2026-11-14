import Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionStableJacquetData
/-!
# An inverse-character functional on the lower induction given by absolutely convergent integrals

JPSS (1983), proof of Lemma (5.5), printed page 424, formulas (1) and (3): the
Whittaker functional on the induced space is a limit of integrals of the scalar
coefficient of a section over the complementary unipotent subgroup against the
conjugate character `θ̄`, and `λ(σ(g) f)` is that integral itself where it converges
absolutely. This module only defines the proposition. It asks for one actual
inverse-character functional on the whole lower induced space that equals that
integral at every section and ambient element where the integrand is integrable. It
asserts no convergence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionLowerJacquetFunctionalStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW

/-- For every inverse-character Whittaker functional `ℓ` of `σ` and every self-dual
Haar measure `ν`, there is one inverse-character Whittaker functional `Λ` of the actual
lower induction `rankOneExtensionLowerModel F t χ σ` such that, for every section `f`
and every `g`, `Λ (I(g) f)` equals the integral of
`y ↦ ℓ(f(u(y) g)) ψ(y_last)` against the row product of `ν` whenever this integrand is
integrable. No integrability is assumed or asserted for any particular `(f, g)`, and
`Λ` is not claimed to be nonzero. -/
def RankOneExtensionLowerJacquetFunctionalStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
    (χ : Quasicharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (ψ : UnitaryAdditiveCharacter F)
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ),
    letI := borel F
    ∃ Λ : Whittaker.glInverseFunctionals ψ (1 + t) (rankOneExtensionLowerModel F t χ σ),
      ∀ (f : rankOneExtensionLowerSection F t χ σ)
        (g : Langlands.GeneralLinear (1 + (t + 1)) F),
        Integrable (rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g)
            (rowMeasure ν.val (t + 1)) →
          Λ.val (rankOneExtensionLowerModel F t χ σ g
              ((rankOneExtensionLowerModel F t χ σ).asModuleEquiv f)) =
            ∫ y, rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g y
              ∂rowMeasure ν.val (t + 1)

end Langlands.AllField.RankinSelberg
