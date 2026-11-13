import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Uniform compact support of unequal-rank Whittaker block coefficients

This proposition is the Whittaker-function support consequence used in the
unequal-rank proof of JPSS Theorem 2.7, printed page 393. It is a statement,
not a proof, and uses the actual coefficient model and block matrix.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- For every coefficient in a Whittaker-type representation, one compact
rectangular set contains all nonzero block evaluations, uniformly in the
smaller general linear group. The supplied topological data are retained. -/
def UnequalRankCompactSupportStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ) : Prop :=
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
          ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F),
            IsCompact C ∧
            ∀ (g : Langlands.GeneralLinear (n + 1) F)
              (x : Matrix (Fin j) (Fin (n + 1)) F),
              f.val.val (unequalRankMatrix j k g x) ≠ 0 → x ∈ C

end Langlands.AllField.RankinSelberg
