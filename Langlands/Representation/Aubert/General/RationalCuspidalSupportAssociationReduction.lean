import Langlands.Representation.Aubert.General.CuspidalJacquetFactorAssociationReduction
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Aubert.General.RootAssociationComposition

/-! # Actual rational support association reduced to cuspidal factor extraction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Actual cuspidal Jacquet-factor extraction implies the exact rational
support-association statement, using an actual common cuspidal Jacquet factor. -/
theorem rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction
    (hExtract : RationalCuspidalJacquetFactorExtractionStatement.{u, v}) :
    RationalCuspidalSupportAssociationStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let : Fintype (SimpleRoot i ν) := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  apply cuspidalSupportAssociationTarget_of_cuspidalJacquetFactors
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (rootAssociation i ν hN hZ)
    (hExtract k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    (rootAssociation_inv i ν hN hZ)
    (rootAssociation_mul i ν hN hZ)
  intro π hπ
  have : π.representation.IsIrreducible := hπ
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X)) π.representation.asModule
  obtain ⟨J, _, τ, hτ, hcτ, hτπ⟩ :=
    exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM π
  exact ⟨J, τ, hτ, hcτ, hτπ⟩

end Langlands.Aubert.General.RationalPointFamily
