import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# All-field port of `Langlands.Representation.RankinSelberg.AnalyticStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.RankinSelberg.AnalyticStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.RankinSelberg
open Langlands.RankinSelberg hiding normalizedAbsoluteValue normalizedAbsoluteValue_apply
open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
universe uF uV uW

/-- Package the already proved residue-cardinality absolute value. No
base-extending spectral norm is substituted for this normalization. -/
def normalizedAbsoluteValue {F : LocalFieldPackage.{uF}}
    (T : F.TopologicalData) : AbsoluteValue F.Carrier ℝ where
  toFun := T.normalizedAbs
  map_mul' := T.normalizedAbs_mul
  nonneg' := T.normalizedAbs_nonneg
  eq_zero' := T.normalizedAbs_eq_zero_iff
  add_le' x y :=
    (T.normalizedAbs_add_le_max x y).trans
      (max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg y))
        (le_add_of_nonneg_left (T.normalizedAbs_nonneg x)))

@[simp] theorem normalizedAbsoluteValue_apply {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) (x : F.Carrier) :
    normalizedAbsoluteValue T x = T.normalizedAbs x := rfl

section WhittakerType
variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end WhittakerType
section EqualRank
variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end EqualRank
section UnequalRank
variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ} (j k : ℕ)
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end UnequalRank
section FixedRanks
variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end FixedRanks
section PadicStatements
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

end PadicStatements
end Langlands.AllFieldBZ.RankinSelberg
