import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenReduction
import Langlands.Geometry.Building.KPZeroOpenness
import Langlands.BruhatTits.Cartan.ActualCentralizerStructureProof
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverTorusProductSmoothProof

/-! # Compact openness of the actual centralizer-zero subgroup -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual subgroup `Z(F)^0` of `P` is compact and open in the canonical
topology on the rational points of `Z = Z_G(S)`. -/
theorem centralizerZeroCompactOpen : P.CentralizerZeroCompactOpenStatement :=
  P.centralizerZeroCompactOpenReduction BruhatTits.Cartan.actualCentralizerStructure
    centralQuotientReductive anisotropicCompactness_proof
    (P.isOpen_centralizerZero derivedCoverTorusProductSmooth
      GaloisNormSmoothnessProof.galoisNormSmoothness)

end Langlands.Geometry.Building.ParahoricBuildingData
