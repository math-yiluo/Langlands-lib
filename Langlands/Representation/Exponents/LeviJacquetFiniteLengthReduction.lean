import Langlands.Representation.Exponents.LeviJacquetFiniteLengthStatement
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Smooth.Admissibility.HoweStatement
import Langlands.Representation.Aubert.General.PrerequisiteStatements

/-! # The represented-parabolic assembly for Renard VI.6.4

This internal reduction retains the four global proof inputs. It does not
prove any of them or the unconditional finite-length target.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finite-length admissibility, Howe's other implication, Jacquet finite type
and Jacquet admissibility imply the unchanged represented VI.6.4 target. -/
def LeviJacquetFiniteLengthReductionStatement : Prop :=
  RationalPointsFiniteLengthAdmissibleStatement.{u, v} →
  SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v} →
  LeviJacquetFiniteTypeStatement.{u, v} →
  ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
  LeviJacquetFiniteLengthStatement.{u, v}

/-- Apply Howe to the actual Levi group with its own canonical topology. -/
theorem leviJacquetFiniteLength_reduction :
    LeviJacquetFiniteLengthReductionStatement.{u, v} := by
  intro hAdmissible hHowe hFiniteType hJacquetAdmissible k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) :=
    leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ
  have hNoetherian : IsNoetherian (MonoidAlgebra ℂ (rationalPoints G))
      π.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hπ).1
  have := hNoetherian
  have hπFinite : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      π.representation.asModule := inferInstance
  have hπAdmissible := hAdmissible k G hG π hπ
  have hJacquet := hJacquetAdmissible k G hG P M U p l r hp hl hr hmul π hπAdmissible
  apply hHowe k M hl.isConnectedReductive
  · exact hFiniteType k G hG P M U p l r hp hl hr hmul π hπFinite
  · exact isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
      (leviPointsEquiv p l hp hl) hJacquet

end Langlands.Aubert.General.RepresentedParabolic
