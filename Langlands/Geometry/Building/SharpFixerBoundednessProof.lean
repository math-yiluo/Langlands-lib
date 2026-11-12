import Langlands.Geometry.Building.SharpFixerBoundednessStructuralReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.BruhatTits.Cartan.ActualCentralizerStructureProof
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof

/-!
# Proof of singleton sharp-fixer boundedness (KP Corollary 7.3.14)

`B.SharpFixerBoundednessStatement` for every actual `B : ValuationBuildingData G`, obtained by
discharging the four structural hypotheses of `sharpFixerBoundedness_of_structure` with their
published proofs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **KP Corollary 7.3.14 for one point.** Under the corrected apartment axioms, every actual
singleton sharp fixer `B.sharpFixer {x}` is algebraically bounded in `G(F)`. -/
theorem sharpFixerBoundedness (B : ValuationBuildingData G) :
    B.SharpFixerBoundednessStatement :=
  B.sharpFixerBoundedness_of_structure rootRankOneFactorization.{u}
    BruhatTits.Cartan.actualCentralizerStructure.{u} centralQuotientReductive.{u}
    anisotropicCompactness_proof.{u}

end Langlands.Geometry.Building.ValuationBuildingData
