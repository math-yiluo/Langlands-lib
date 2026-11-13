import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Unequal-rank bilinear uniqueness for Whittaker-type coefficient models

The covariance is JPSS (2.11.2) and (2.11.4). The full Whittaker-type
uniqueness target is an internal extension needed for the scope of Theorem
2.7; the printed Proposition on p.399 assumes irreducible generic data.
This module states the extension and does not prove it.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end FixedData

/-- Full Whittaker-type unequal-rank bilinear uniqueness outside a finite
set of spectral values. This internal extension of the irreducible generic
Proposition in JPSS Section 2.11 remains a proof obligation. -/
def UnequalRankBilinearUniquenessStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) : Prop :=
  letI := T.topology
  ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        let M := (coefficientModel π ℓ).toSubmodule
        let M' := (coefficientModel σ ℓ').toSubmodule
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          ∀ B B' : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ,
            IsUnequalRankBilinearCovariant hnr ψ (normalizedAbsoluteValue T)
              π σ ℓ ℓ' s B →
            IsUnequalRankBilinearCovariant hnr ψ (normalizedAbsoluteValue T)
              π σ ℓ ℓ' s B' →
            B ≠ 0 → ∃ c : ℂ, B' = c • B

end Langlands.AllField.RankinSelberg
