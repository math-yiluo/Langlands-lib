import Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslationReduction
import Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityProof

/-!
# The translation part of AS 5 for quasi-split adjoint groups

This module proves `ValuationBuildingQuasiSplitAdjointTranslationStatement` by applying the
published reduction `valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity`
to the published proof `quasiSplitAdjointSimpleRootTransitivity` of
`QuasiSplitAdjointSimpleRootTransitivityStatement`.
-/

universe u

namespace Langlands.Geometry.Building

/-- The translation part of AS 5 (Kaletha–Prasad Proposition 6.6.2, via Lemma 6.4.10). -/
theorem valuationBuildingQuasiSplitAdjointTranslation :
    ValuationBuildingQuasiSplitAdjointTranslationStatement.{u} :=
  valuationBuildingQuasiSplitAdjointTranslation_of_simpleRootTransitivity
    quasiSplitAdjointSimpleRootTransitivity

end Langlands.Geometry.Building
