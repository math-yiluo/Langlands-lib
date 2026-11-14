import Langlands.Representation.RankinSelberg.LocalFieldUnequalRankAnalyticStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof

/-!
# From supplied local-field data to the hypothesized normalization, for Theorem 2.7

The all-field port states JPSS 1983, Theorem (2.7)(i)–(ii) for a field `F` with supplied
data `T : LocalFieldData F`, Borel structures, the residue cardinality
`T.residueCardinality` and the absolute value `normalizedAbsoluteValue T`. The statement
`LocalFieldUnequalRankAnalyticStatement` instead takes ambient instances, arbitrary Borel
structures, and a hypothesized pair `q`, `abv` normalized by a uniformizing element `ϖ`.
This module shows that the ported statement at `T := LocalFieldData.ofInstances F`, for
every field and every block, implies it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF uV uW

/-- The ported all-field Theorem (2.7)(i)–(ii) at the ambient data, for every field and
every block, implies `LocalFieldUnequalRankAnalyticStatement` with hypothesized `q`, `abv`,
`ϖ` and arbitrary Borel structures. -/
theorem localFieldUnequalRankAnalytic_of_allField
    (h : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (n j k : ℕ),
      Langlands.AllField.RankinSelberg.UnequalRankAnalyticStatement.{uF, uV, uW} F
        (LocalFieldData.ofInstances F) n j k) :
    LocalFieldUnequalRankAnalyticStatement.{uF, uV, uW} := by
  intro F _ _ _ _ _ _ mF hF n j k mG hG mU hU mQ hQ q hq abv ϖ hϖ habv hunit ψ hInv μ hμ
    ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain rfl := hF.measurable_eq
  obtain rfl := hG.measurable_eq
  obtain rfl := hU.measurable_eq
  obtain rfl := hQ.measurable_eq
  have habvT :=
    Langlands.AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ
      habv hunit
  have hqT : q = (LocalFieldData.ofInstances F).residueCardinality :=
    hq.trans Langlands.AllField.RankinSelberg.residueCardinality_ofInstances.symm
  subst habvT hqT
  exact @h F _ _ _ _ n j k ψ hInv μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'

/-- JPSS 1983, Theorem (2.7)(i)–(ii), over every nonarchimedean local field with ambient
instances: the statement `LocalFieldUnequalRankAnalyticStatement` holds. -/
theorem localFieldUnequalRankAnalytic : LocalFieldUnequalRankAnalyticStatement.{uF, uV, uW} :=
  localFieldUnequalRankAnalytic_of_allField fun F _ _ _ _ n j k =>
    Langlands.AllField.RankinSelberg.unequalRankAnalytic.{uF, uV, uW} F
      (LocalFieldData.ofInstances F) n j k

end Langlands.RankinSelberg
