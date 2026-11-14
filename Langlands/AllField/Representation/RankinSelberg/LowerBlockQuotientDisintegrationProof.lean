import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationProof
import Langlands.AllField.Group.GL.LowerBlockQuotientGeometryProof
import Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison
/-!
# Proof of the lower-block quotient disintegration

The geometry conjuncts come from `lowerBlockQuotientGeometry`, the measure identity
from `lowerBlockQuotient_eq_smul_map_chart` with the right Haar measure
`lowerTriangularRightHaar` on `B⁻_d`, and the integral conjuncts from
`complex_integral_transfer_of_positive_scaled_map`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientDisintegrationStatement LowerBlockQuotientGeometryStatement comap_lowerTriangularQuotientMap_properties continuous_lowerBlockQuotientDensity continuous_lowerTriangularBlockDensity lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk lowerBlockQuotientDisintegration lowerBlockQuotientGeometry lowerBlockQuotient_eq_smul_map_chart lowerTriangularBlockDensity lowerTriangularBlockDensity_eq_coe lowerTriangularQuotientMap_comap_of_isCompatible lowerTriangularQuotientMap_measurableEmbedding lowerTriangularQuotientMap_mul lowerTriangularRightHaar lowerTriangularRightHaar_properties map_lowerTriangularBlockDensity_mulRight map_rectangularMeasure_mulRight measurable_lowerBlockQuotientDensity measurePreserving_lowerBlockWeightedProduct_diagonal measurePreserving_lowerBlockWeightedProduct_mulRight measurePreserving_lowerBlockWeightedProduct_shear rectangularMeasure_compactOpen_pos_lt_top
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding continuous_lowerBlockCellParameters exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerBlockQuotientChart isOpenEmbedding_lowerTriangularQuotientMap isOpenMap_lowerBlockQuotientChart isOpenMap_lowerBlockQuotientChart_comp_cellParameters isOpen_upperUnipotent_mul_lowerTriangular_inter lowerBlockQuotientChart_range_compl_null measurable_lowerBlockQuotientChart padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

/-- Proof of `LowerBlockQuotientDisintegrationStatement`. -/
theorem lowerBlockQuotientDisintegration : LowerBlockQuotientDisintegrationStatement.{uF} := by
  intro F _ _ _ _ n k
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  have : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (n + 1) F))
  have : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F)) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1 + k + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + k + 1) F)
  have : BorelSpace (upperUnipotent (n + 1 + k + 1) F) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F))
  have : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F)) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (k + 1) F)
  have : BorelSpace (lowerTriangularSubgroup (k + 1) F) := ⟨rfl⟩
  intro chart D η dx _ _ μa μad hμa hμad
  obtain ⟨hreg, hσ, hpos, hfin, hrinv, hK⟩ := lowerTriangularRightHaar_properties F T (k + 1)
  let ρ := lowerTriangularRightHaar F T (k + 1)
  have hρ : ρ ≠ 0 := NeZero.ne ρ
  obtain ⟨C, hC, hμ⟩ := lowerBlockQuotient_eq_smul_map_chart T (n + 1) (k + 1) η
    (generalLinearHaar F n) (unipotentHaar F n)
    (generalLinearHaar F (n + 1 + k)) (unipotentHaar F (n + 1 + k))
    μa μad hμa hμad ρ hρ
  have hgeom := lowerBlockQuotientGeometry F n k μad hμad
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2,
    rectangularMeasure_compactOpen_pos_lt_top F T (k + 1) (n + 1) η, ρ, hreg, hσ, hpos, hfin,
    hrinv, hK, C, hC, hμ, fun f hf => ?_⟩
  obtain ⟨h1, h2⟩ := complex_integral_transfer_of_positive_scaled_map _ μad chart hgeom.2.1 C hC
    hμ f hf
  exact ⟨h1, fun _ => h2⟩

end Langlands.AllField.RankinSelberg
