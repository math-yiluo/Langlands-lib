import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Full Whittaker type of normalized upper block induction

The forward preservation assertion derived from JPSS (1983), Sections 2.1 and
2.3, in the actual normalized upper-block convention of
`GammaMultiplicativityStatement`. This is a proposition definition, not a proof.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uW

/-- Normalized upper block induction preserves full Whittaker type for arbitrary
admissible finite-type block representations, including reducible ones.
The conclusion includes admissibility, finite generation over the group algebra,
and a linear equivalence of the entire Whittaker-functional space with `ℂ`. -/
def NormalizedProductWhittakerTypeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (t k : ℕ) (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
    (IsOfWhittakerType t (standardCharacter ψ t)
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))

end Langlands.AllField.RankinSelberg
