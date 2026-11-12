import Langlands.Geometry.Building.KPCentralizerParahoricAssembly
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.Geometry.Building.SharpFixerBoundednessProof
import Langlands.Geometry.Building.KPMinimalLeviZeroComparisonProof

/-!
# Proof of the centralizer part of parahoric subgroups (KP Lemma 7.4.3)

`P.CentralizerParahoricIntersectionStatement` for every actual `P : ParahoricBuildingData G`,
obtained by discharging the three inputs of the conditional assembly
`centralizerParahoricAssembly`: root lifting through the actual simply connected cover (from the
apartment premise), singleton sharp-fixer boundedness (KP Corollary 7.3.14) and the cover-image
comparison (KP Corollary 2.6.28).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **KP Lemma 7.4.3.** Under the corrected apartment axioms, for every non-empty `Ω ⊆ A(S)`,
`Z(F) ∩ G(F)^0_Ω = Z(F)^0` for the actual centralizer `Z` of `S` and its actual `Z(F)^0`. -/
theorem centralizerParahoricIntersection (P : ParahoricBuildingData G) :
    P.CentralizerParahoricIntersectionStatement := fun hax =>
  P.centralizerParahoricAssembly (P.rootGroup_le_simplyConnectedImage hax)
    P.toValuationBuildingData.sharpFixerBoundedness
    (P.zeroDatum.coverImageCentralizerNormKernel_of_intersection
      P.zeroDatum.minimalLeviZeroComparison.2) hax

end Langlands.Geometry.Building.ParahoricBuildingData
