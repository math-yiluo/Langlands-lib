import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Corrected finite Weil restriction point homeomorphism

Conrad's Proposition 5.11(1), with the explicit module-topology hypothesis used in
Example 2.4. The unrestricted source statement fails for some purely inseparable
extensions of incomplete henselian fields; see the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Corrected Conrad Proposition 5.11(1): for a finite extension of henselian
nontrivially normed fields carrying the module topology, the Weil restriction of a
quasi-separated finite-type algebraic space exists as an algebraic space, and its
canonical rational-point equivalence is a homeomorphism for the independently
defined étale-chart topologies. -/
def HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement : Prop :=
  ∀ (K K' : Type u) [NontriviallyNormedField K] [NontriviallyNormedField K']
    [NormedAlgebra K K'] [FiniteDimensional K K'] [IsModuleTopology K K'],
    IsHenselianValuedField K → IsHenselianValuedField K' →
    ∀ Y' : AlgebraicSpace (Spec (CommRingCat.of K')),
      IsQuasiSeparated Y' → FiniteTypeOverRing K' Y' →
        ∃ h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf),
          @IsHomeomorph _ _ (etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h))
            (etaleChartTopology K' Y') (ringWeilRestrictionBasePointsEquiv K K' Y' h)

end Langlands.AlgebraicGeometry.AlgebraicSpace
