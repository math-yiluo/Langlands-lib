import Langlands.Group.GL.LowerBlockQuotientGeometryProof
import Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison
import Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement

/-!
# Proof of the lower-block quotient disintegration

The geometry conjuncts come from `lowerBlockQuotientGeometry`, the measure identity
from `lowerBlockQuotient_eq_smul_map_chart` with the right Haar measure
`lowerTriangularRightHaar` on `B⁻_d`, and the integral conjuncts from
`complex_integral_transfer_of_positive_scaled_map`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear QuotientIntegration
open scoped ENNReal

universe uF

/-- Proof of `LowerBlockQuotientDisintegrationStatement`. -/
theorem lowerBlockQuotientDisintegration : LowerBlockQuotientDisintegrationStatement.{uF} := by
  intro p _ F n k
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (n + 1) F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F.Carrier)) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + k + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier)) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
  intro chart D η dx _ _ μa μad hμa hμad
  obtain ⟨hreg, hσ, hpos, hfin, hrinv, hK⟩ := lowerTriangularRightHaar_properties F T (k + 1)
  let ρ := lowerTriangularRightHaar F T (k + 1)
  have hρ : ρ ≠ 0 := NeZero.ne ρ
  obtain ⟨C, hC, hμ⟩ := lowerBlockQuotient_eq_smul_map_chart T (n + 1) (k + 1) η
    (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n)
    (generalLinearHaar F.Carrier (n + 1 + k)) (unipotentHaar F.Carrier (n + 1 + k))
    μa μad hμa hμad ρ hρ
  have hgeom := lowerBlockQuotientGeometry p F n k μad hμad
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2,
    rectangularMeasure_compactOpen_pos_lt_top F T (k + 1) (n + 1) η, ρ, hreg, hσ, hpos, hfin,
    hrinv, hK, C, hC, hμ, fun f hf => ?_⟩
  obtain ⟨h1, h2⟩ := complex_integral_transfer_of_positive_scaled_map _ μad chart hgeom.2.1 C hC
    hμ f hf
  exact ⟨h1, fun _ => h2⟩

end Langlands.RankinSelberg
