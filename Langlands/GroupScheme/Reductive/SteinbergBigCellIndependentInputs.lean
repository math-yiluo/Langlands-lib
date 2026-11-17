import Langlands.GroupScheme.Reductive.SuppliedRootSteinbergBigCell
import Langlands.GroupScheme.Reductive.LinkedRootsFromStructuralStatements
import Langlands.GroupScheme.Reductive.CanonicalRhoOppositePairCovering
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # The unchanged Steinberg target from explicit independent structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

/-- The remaining structural propositions, each retained as an explicit assumption.
This record neither proves them nor certifies the independence of a supplied proof. -/
structure IndependentSteinbergInputs : Prop where
  rootData : RootDatumExistenceStatement.{u}
  rootCells : SplitRankOneRootCellStatement.{u}
  rootLines : SplitRootLieLineStatement.{u}
  corootGeneration : SplitSimplyConnectedCorootSpanStatement.{u}
  oppositePairs : AlgClosedOppositeFactorPairsStatement.{u}

/-- Construct the actual seven-law witnesses from the explicit structural propositions.
No existing unconditional Steinberg, Borel, root-cell or root-line proof supplies a field. -/
def SteinbergBigCellData.ofIndependentInputs (h : IndependentSteinbergInputs.{u})
    (k : Type u) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsSimplyConnected G) : SteinbergBigCellData G :=
  Classical.choice <| by
    let hred := hG.isSemisimple.isConnectedReductive
    let : Smooth G.X.hom := hred.smooth
    obtain ⟨T, i, hi, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed G
    let p := SplitPinning.ofRootDatumExistence h.rootData hred hT i hi
      (h.rootLines k G hred T hT i hi)
    let : Fintype p.rootIndex := Fintype.ofFinite _
    have hspan : p.rootDatum.corootSpan ℤ = ⊤ :=
      h.corootGeneration k G hG p.torus p.isSplitTorus p.inclusion p.isMaximalTorus
        p.rootIndex p.rootDatum p.isRootDatum p.isReduced
    let c := p.simpleRootCoordinatesOfStructuralStatements h.rootCells h.rootLines
    have hcover := p.isRootDatum.borelTorusBruhatCovering_polarization_rho_of_statement
      p.base hspan p.isConnectedReductive p.isSplitTorus p.isMaximalTorus h.oppositePairs
    exact ⟨p.suppliedRootSteinbergBigCellData c hspan q Fact.out hcover⟩

/-- These explicit structural propositions imply precisely the unchanged Library target.
Their proofs remain obligations; this conditional implication is not an exact-target proof. -/
theorem IndependentSteinbergInputs.to_statement (h : IndependentSteinbergInputs.{u}) :
    SteinbergBigCellStatement.{u} := by
  intro k _ _ q _ _ G _ hG
  exact (SteinbergBigCellData.ofIndependentInputs h k q G hG).exists_data

end Langlands.GroupScheme
