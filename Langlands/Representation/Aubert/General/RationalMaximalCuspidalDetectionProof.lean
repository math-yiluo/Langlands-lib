import Langlands.Representation.Aubert.General.RationalRankOneLengthInputsStatement
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Aubert.General.RankOneJacquetAssembly
import Langlands.Representation.Aubert.General.MaximalRootAssociation
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof

/-! # Maximal-Levi Jacquet detection from cuspidal factor extraction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Actual cuspidal factor extraction implies detection of every irreducible
subquotient by a maximal proper standard Jacquet module. -/
theorem rationalMaximalCuspidalJacquetDetectionFromExtraction :
    RationalMaximalCuspidalJacquetDetectionFromExtractionStatement.{u, v} := by
  intro hext k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro J hJ σ hσ hcusp D hD hDsub
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  let : D.representation.IsIrreducible := hD
  have : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X))
      D.representation.asModule
  obtain ⟨I, hInz, τ, hτ, hτcusp, hτsub⟩ :=
    exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM D
  have hσcusp := (isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v}
    (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν) (hU := hU)
    J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) σ).mp hcusp
  obtain ⟨n, _, hassoc, _⟩ :=
    hext k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
      J I σ D τ hσ hσcusp hτ hτcusp hDsub hτsub
  obtain ⟨β, rfl⟩ := rootAssociation_isMaximalStandard i ν hN hZ hassoc hJ
  exact ⟨β, hInz⟩

end Langlands.Aubert.General.RationalPointFamily
