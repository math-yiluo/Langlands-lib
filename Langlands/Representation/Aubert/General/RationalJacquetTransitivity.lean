import Langlands.Representation.Aubert.General.RationalHaarModulus
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction

/-! # Rational normalized Jacquet transitivity from the standard projections -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance rationalJacquetTransitivityPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hproj : ∀ A : Finset (SimpleRoot i ν), Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (J : Finset (SimpleRoot i ν)) (I : Finset J)

/-- Actual normalized Jacquet restriction in stages, with the Haar-character
identity derived from continuity of the standard projections. -/
def standardJacquetStagesIso_of_standardProjection
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
    (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J))) :
    jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J) ⋙
      leviNormalizedJacquetFunctor hM
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ≅
    jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex J I)) (hU (leviIndex J I)) :=
  standardJacquetStagesIso i ν hInter hG hi hν hStandard hU J I hM hWc
    (standardJacquetModulus_stages i ν hInter hG hi hν hStandard hproj J I hU hM)

/-- Actual normalized Jacquet restriction in stages from the topological and
structural premises of the rational involutivity reduction. -/
def standardJacquetStagesIso_of_premises
    [T2Space (RationalPoint k G.X)]
    (hP : ∀ A, IsClosed (parabolic i ν A : Set (RationalPoint k G.X)))
    (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A)) :
    jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J) ⋙
      leviNormalizedJacquetFunctor
        (levi_isClosed i ν hStandard hG hi hν hP hproj J)
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ≅
    jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex J I)) (hU (leviIndex J I)) :=
  standardJacquetStagesIso_of_standardProjection
    i ν hInter hG hi hν hStandard hU hproj J I
    (levi_isClosed i ν hStandard hG hi hν hP hproj J)
    (isLimitOfCompactSubgroups_leviUnipotent i ν hStandard hG hi hν hP hproj hUc J I)

end Langlands.Aubert.General.RationalPointFamily
