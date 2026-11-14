import Langlands.Representation.RankinSelberg.LocalConverseStatement
import Langlands.AllField.LocalFactor.Abelian.Padic
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-!
# Henniart's local converse theorems for epsilon factors of pairs

Henniart 1993, printed page 340, Corollary: two supercuspidal representations
of `GL_n(F)`, `n ≥ 2`, with the same epsilon factors of pairs against every
supercuspidal representation of `GL_r(F)`, `1 ≤ r ≤ n - 1`, are equivalent. The
epsilon factors are the JPSS relation `IsPairEpsilonFactor` with the self-dual
measure; agreement means one common factor value.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW


/-- The epsilon-factor relation for actual representations of `GL_(r+1)(F)` and
`GL_(n+1)(F)` over a p-adic field with its canonical topological data: `q` is
the residue cardinality and the absolute value is the normalized one. -/
def IsPadicPairEpsilonFactor (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (e : ℂˣ × ℤ) : Prop :=
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  IsPairEpsilonFactor (⟨⟩ : LocalFieldData F).residueCardinality ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) ν π σ e

end Langlands.AllField.RankinSelberg
