import Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Finite Schwartz expansion of unequal-rank block coefficients

This proposition isolates the pointwise smoothness-and-compactness reduction
behind JPSS, printed pages 393–394. Uniform compact support is an explicit
premise. This module states the reduction and does not prove it.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankFiniteExpansionStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Uniform compact support in the rectangular variable implies a finite,
pointwise Schwartz expansion using coefficients of the same representation
and functional, evaluated on the same larger group's diagonal block. -/
def UnequalRankFiniteExpansionStatement (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V,
      IsOfWhittakerType (n + (j + k + 1))
        (standardCharacter ψ (n + (j + k + 1))) π →
      ∀ ℓ : glFunctionals ψ (n + (j + k + 1)) π,
        ℓ.val ≠ 0 →
        ∀ f : (coefficientModel π ℓ).toSubmodule,
          (∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F),
            IsCompact C ∧ ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
              f.val.val (unequalRankMatrix j k g x) ≠ 0 → x ∈ C) →
          ∃ (m : ℕ)
            (φ : Fin m → SchwartzBruhat (Matrix (Fin j) (Fin (n + 1)) F))
            (fs : Fin m → (coefficientModel π ℓ).toSubmodule),
            ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
              f.val.val (unequalRankMatrix j k g x) =
                ∑ i : Fin m, φ i x * (fs i).val.val (appendIdentity n (j + k + 1) g)

end Langlands.AllField.RankinSelberg
