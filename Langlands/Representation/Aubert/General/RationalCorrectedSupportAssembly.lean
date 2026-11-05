import Langlands.Representation.Aubert.General.CorrectedSupportBoundary
import Langlands.Representation.Aubert.General.RationalCorrectedSupportComparison
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport

/-! # Rational fixed-order support from two structural prerequisites -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The two remaining uniform inputs to the actual rational support assembly.
This predicate asserts neither input, and does not change the rational target. -/
def RationalCorrectedSupportPrerequisites : Prop :=
  StandardParabolicPointsStatement.{u} ∧
    BruhatTits.DynamicParabolicQuotientCompactStatement.{u}

/-- The unchanged whole rational target follows from the two named structural
prerequisites. All topology and Coxeter inputs of that target are retained. -/
theorem rationalCorrectedSurvivingSupportStatement_of_prerequisites
    (hInputs : RationalCorrectedSupportPrerequisites.{u}) :
    RationalCorrectedSurvivingSupportStatement.{u} := by
  obtain ⟨hPoints, hcompact⟩ := hInputs
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder _hInter hRoots hN hZ _hU _hM _hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _
  let : DecidableEq (Weyl i) := Classical.decEq _
  intro CM cs _hLength _hPositive hLevi
  let := compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν ∅
  exact CorrectedFiltration.survivingSupportTarget_of_parabolicComparisons
    (parabolic i ν) (torusPoints i) cs
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (isClosed_standard_parabolic i ν hStandard hG hi hν)
    (isBruhatCover_of_standardParabolicPoints i ν hPoints hG hi hν ∅)
    (fun J I => parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints
      i ν hPoints hG hi hν hN hZ cs hLevi J I)

end Langlands.Aubert.General.RationalPointFamily
