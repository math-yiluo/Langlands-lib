import Langlands.GroupScheme.Reductive.SteinbergBigCellStructuralAssembly
import Langlands.GroupScheme.Rational.DominantHighestWeightProof

/-! # Steinberg big-cell assembly from root and coroot inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Construct complete data using the proved highest-weight existence and height
irreducibility theorems. Root-datum existence and coroot span remain explicit. -/
def steinbergBigCellDataOfRootAndCoroot
    (hroot : RootDatumExistenceStatement.{u})
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsSimplyConnected G) :
    SteinbergBigCellData G :=
  steinbergBigCellDataOfStructuralInputs hroot hcoroot
    splitDominantHighestWeightRepresentationsExist k q G hG

/-- The unchanged host follows from the two remaining structural inputs. -/
theorem steinbergBigCell_of_rootAndCoroot
    (hroot : RootDatumExistenceStatement.{u})
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u}) :
    SteinbergBigCellStatement.{u} :=
  steinbergBigCell_of_structuralInputs hroot hcoroot
    splitDominantHighestWeightRepresentationsExist

end Langlands.GroupScheme
