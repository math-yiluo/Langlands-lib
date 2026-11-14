import Langlands.Representation.Conductor.SphericalCorankOneReduction
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement
import Langlands.Representation.RankinSelberg.LocalFieldUnramifiedTestTwist

/-!
# The multiplicativity input of the corank-one reduction

`PrincipalSeriesGammaInput` follows from the all-field multiplicativity statement
for `π × I(z)` and the published unramified twist identity for rank-one tests
(`isGeneralPairGammaFactor_unramifiedTest`).
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open Langlands.RankinSelberg LocalFactor Langlands.GeneralLinear.Iwasawa
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV

/-- The multiplicativity input of the reduction, from the all-field multiplicativity
statement for `π × I(z)` and the published rank-one unramified twist. -/
theorem principalSeriesGammaInput_of_multiplicativity
    (hMult : LocalFieldPrincipalSeriesGammaMultiplicativityStatement.{uF, uV}) :
    PrincipalSeriesGammaInput.{uF, uV} := by
  intro F _ _ _ _ _ _ mF bF n mGL bGL mU bU mQ mQ0 mGL1 bGL1 mU1 bU1 q ψ abv ϖ μ h ν hν
    V _ _ π hπ G hG x _
  have hq1 : 1 < q := h.one_lt_q
  have hW := isOfWhittakerType_of_isGeneric_localField hπ
  have hqR : IsResidueCardinality (F := F) q := h.residueCardinality
  have hϖ := h.uniformizer
  have habv := h.abv_uniformizer
  have habv1 := h.abv_unit
  have eQ := h.borel.measurable_eq
  have eQ0 := h.borel_rankOne.measurable_eq
  have eF := bF.measurable_eq
  have eGL := bGL.measurable_eq
  have eU := bU.measurable_eq
  have eGL1 := bGL1.measurable_eq
  have eU1 := bU1.measurable_eq
  subst eQ eQ0 eF eGL eU eGL1 eU1
  obtain ⟨Gs, hGs, hprod⟩ := hMult F q hqR abv ϖ hϖ habv habv1 ψ ν hν (n + 1) n π hW x
  have hGi : ∀ i, Gs i = rationalRescale (x i) G := fun i =>
    ((isGeneralSymmetricGammaFactor_of_le (Nat.zero_le _)).mp (hGs i)).unique hq1
      (isGeneralPairGammaFactor_unramifiedTest hq1 hϖ habv habv1 (x i) π hG)
  have hP := (isGeneralSymmetricGammaFactor_of_le (Nat.le_succ n)).mp hprod
  rw [Finset.prod_congr rfl (fun i _ => hGi i)] at hP
  exact hP

end Langlands.Conductor.SphericalCorankOne
