import Langlands.Representation.Plancherel.RenardActualLattice
import Langlands.Representation.Plancherel.RenardDominantSections
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Actual dominant centralizer sections and finite positive covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.RenardCartan

/-- The exact dominant comparison, for all of the published actual data. -/
theorem renardDominantComparison : RenardDominantComparisonStatement.{u} := by
  intro F _ _ _ _ G _ hG S i hi ν _ Z j _ _ s _ h
  let : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  exact dominantCentralizerLatticeConclusions_of_latticeComparison s h i ν
    (hS.finite_positiveRelativeRoots i ν)
    (finiteIndex_splitValuationImage_of_comparison s h hS)
    (bijOn_C0_splitValuationImage_of_comparison s h hS)

end Langlands.Plancherel.RenardCartan
