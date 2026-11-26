import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Exponents.CasselmanFromBuildingProof
import Langlands.Representation.Exponents.LeviInductionNormalizedTemperedProof
import Langlands.Representation.Exponents.SquareIntegrableNormalizedTemperedProof
import Langlands.Representation.Exponents.TemperedCentralCharacterData
import Langlands.Representation.Exponents.TemperedDiscreteSeriesFromBuildingStatement
import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesReduction
import Langlands.Representation.Exponents.TemperedPositiveJacquetExponents

/-! # The tempered square-integrability criterion and discrete series from building data -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The tempered square-integrability criterion, discrete-series embedding equivalence
and unitarizability follow from existence of data satisfying the one-group building axioms. -/
theorem temperedDiscreteSeriesFromBuilding :
    TemperedDiscreteSeriesFromBuildingStatement.{u, v} := by
  intro hGroup
  have hCasselman := casselmanFromBuilding.{u, v}
    (Geometry.Building.bruhatTitsAvailabilityReduction hGroup)
  have hCriterion : TemperedSquareIntegrableUnitaryPartStatement.{u, v} := by
    intro k _ _ _ _ _ G hG
    have := hG.isAffineHom
    have := hG.smooth
    let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    intro _ _ _ _ haar _ π ω hπ hω
    exact (hCasselman k G hG haar π hπ.isAdmissible
      ⟨hπ.unitaryCentralCharacter hω⟩).trans
      (hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish hG π hπ)
  have hDiscrete := temperedIrreducibleDiscreteSeries_of_inputs
    squareIntegrableNormalizedTempered leviInductionNormalizedTempered
    arbitraryParabolicQuotientCompact hCriterion
  exact ⟨hCriterion, hDiscrete, temperedIrreducibleUnitarizable_of_discreteSeries
    hDiscrete RationalPointFamily.rationalReductiveUnimodularity
    standardCocharacter arbitraryParabolicQuotientCompact⟩

end Langlands.Aubert.General.RepresentedParabolic
