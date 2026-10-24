import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Uniform compact support of unequal-rank Whittaker block coefficients

This proposition is the Whittaker-function support consequence used in the
unequal-rank proof of JPSS Theorem 2.7, printed page 393. It is a statement,
not a proof, and uses the actual coefficient model and block matrix.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- For every coefficient in a Whittaker-type representation, one compact
rectangular set contains all nonzero block evaluations, uniformly in the
smaller general linear group. The supplied topological data are retained. -/
def UnequalRankCompactSupportStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V,
      IsOfWhittakerType (n + (j + k + 1))
        (standardCharacter ψ (n + (j + k + 1))) π →
      ∀ ℓ : glFunctionals ψ (n + (j + k + 1)) π,
        ℓ.val ≠ 0 →
        ∀ f : (coefficientModel π ℓ).toSubmodule,
          ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
            IsCompact C ∧
            ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
              (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier),
              f.val.val (unequalRankMatrix j k g x) ≠ 0 → x ∈ C

end Langlands.RankinSelberg
