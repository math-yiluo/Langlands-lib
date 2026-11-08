import Langlands.GroupScheme.Reductive.SteinbergBigCellHostAssembly
import Langlands.GroupScheme.Reductive.CanonicalRhoHeightIrreducibility

/-! # Steinberg big-cell assembly with the height input discharged -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The proved full-space height theorem supplies the global height interface.
The highest-weight representation remains supplied inside that interface. -/
theorem splitSteinbergHeightIrreducibility :
    SplitSteinbergHeightIrreducibilityStatement.{u} := by
  intro k _ _ G _ p _ hspan q _ _
  exact p.canonicalRhoSteinbergHeightIrreducibility hspan q

/-- Construct complete data from three explicit global inputs. Per-height
irreducibility of the entire canonical covariant space is now proved. -/
def steinbergBigCellDataOfStructuralInputs
    (hroot : RootDatumExistenceStatement.{u})
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u})
    (hhw : SplitDominantHighestWeightRepresentationsExistStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsSimplyConnected G) :
    SteinbergBigCellData G :=
  steinbergBigCellDataOfInputs
    ⟨hroot, hcoroot, hhw, splitSteinbergHeightIrreducibility⟩ k q G hG

/-- The unchanged host follows from the three remaining explicit inputs.
This theorem does not discharge their existence or integral-generation claims. -/
theorem steinbergBigCell_of_structuralInputs
    (hroot : RootDatumExistenceStatement.{u})
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u})
    (hhw : SplitDominantHighestWeightRepresentationsExistStatement.{u}) :
    SteinbergBigCellStatement.{u} :=
  steinbergBigCell_of_inputs
    ⟨hroot, hcoroot, hhw, splitSteinbergHeightIrreducibility⟩

end Langlands.GroupScheme
