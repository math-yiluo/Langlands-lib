import Langlands.Representation.Aubert.General.RationalRankOneGeometricJacquetProof
import Langlands.Representation.Aubert.General.RationalCoatomGeometricBudget
import Langlands.Representation.Aubert.General.RationalRankOneLengthInputsStatement
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons

/-! # The coatom Jacquet-length budget on actual reductive rational points -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open Classical GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- A maximal-source actual geometric filtration theorem suffices for the whole
coatom budget. Its additional Weyl and Coxeter premises are discharged. -/
theorem rationalMaximalCuspidalJacquetBudget_of_maximalSourceFiltration :
    RationalMaximalSourceGeometricFiltrationStatement.{u, v} →
      RationalMaximalCuspidalJacquetBudgetStatement.{u, v} := by
  intro hFil k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro J hJ σ hσ hc
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  let d := rootSpanPointCoxeterData i ν hN hZ hG hi hRoots hν
  let : Finite (Weyl i) := d.finiteWeyl
  let : Fintype (Weyl i) := Fintype.ofFinite _
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ d.system hi.isSplitSubtorus.1 hRoots hν d.rootLength
  have hExists : ∀ a : SimpleRoot i ν,
      Nonempty (PointGeometricObjectFiltration.{u, v}
        i ν hG hi hν hStandard hM hU d.system (Finset.univ.erase a) J σ) := by
    intro a
    apply hFil k G hG T i hi ν hν hStandard hInter hRoots hU hM
      hN hZ d.matrix d.system d.rootLength hSimple d.leviWeyl
      (minimalityLengthCriterion_proof d.system) (associatedSubsetLaws_proof d.system)
      J hJ σ (Finset.univ.erase a)
    exact Finset.erase_ne_self.mpr (Finset.mem_univ a)
  let s := fun a => Classical.choice (hExists a)
  change (∑ a, repLength (pointInducedJacquetObject i ν hG hi hν hStandard hU
    (Finset.univ.erase a) J σ).representation) ≤ 2
  apply pointCoatomJacquetBudget_of_geometricFiltrations.{u, v}
    i ν hN hZ d.system d.rootLength hSimple hG hi hν hStandard hInter hM hU
    J hJ σ hσ hc (fun a => (s a).tailLength + 1)
    (fun a q => ((s a).enumeration q).val)
    (fun a q => (mem_minimalReps d.system _ _ _).mp ((s a).enumeration q).property)
    (fun a => Subtype.val_injective.comp (s a).enumeration.injective)
    (fun a => (s a).lift) (fun a => (s a).lift_class)
    (fun a => (s a).source) (fun a => (s a).target)
    (fun a => (s a).filtration) (fun a => (s a).grade)

/-- The complete actual coatom Jacquet-length budget, with no parameters
outside the published proposition. -/
theorem rationalMaximalCuspidalJacquetBudget :
    RationalMaximalCuspidalJacquetBudgetStatement.{u, v} :=
  rationalMaximalCuspidalJacquetBudget_of_maximalSourceFiltration.{u, v}
    rationalMaximalSourceGeometricFiltration.{u, v}

end Langlands.Aubert.General.RationalPointFamily
