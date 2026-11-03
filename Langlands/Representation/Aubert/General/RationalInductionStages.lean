import Langlands.Representation.Aubert.General.InductionStages
import Langlands.Representation.Aubert.General.RationalHaarModulus
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction

/-! # Normalized induction in stages for the actual rational standard family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance rationalInductionStagesPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hproj : ∀ A : Finset (SimpleRoot i ν), Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A))
  (J : Finset (SimpleRoot i ν)) (I : Finset J)

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

/-- Actual normalized induction in stages. The positive Haar-modulus product
is derived from the standard projection and rational-point premises. -/
def standardInductionStagesIso
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
    (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J))) :
    leviNormalizedInductionFunctor.{u, max (u + 1) v} hM
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ⋙
      normalizedInductionFunctor (dec J) (hU J) ≅
    normalizedInductionFunctor (dec (leviIndex J I)) (hU (leviIndex J I)) := by
  exact normalizedInductionStagesIso
    (dec (leviIndex J I)) (dec J) hM
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hU J) (hUc (leviIndex J I)) (hUc J) hWc
    (standardJacquetModulus_stages i ν hInter hG hi hν hStandard hproj J I hU hM)
    (parabolic_le_of_subset i ν hInter hG hi hν hStandard
      _ J (leviIndex_subset J I))
    (unipotent_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (hproj J)

/-- Closedness of the standard Levi and the inner compact-limit condition
follow from the ambient parabolic, projection, and compact-limit premises. -/
def standardInductionStagesIso_of_premises
    [T2Space (RationalPoint k G.X)]
    (hP : ∀ A, IsClosed (parabolic i ν A : Set (RationalPoint k G.X))) :
    leviNormalizedInductionFunctor.{u, max (u + 1) v}
        (levi_isClosed i ν hStandard hG hi hν hP hproj J)
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ⋙
      normalizedInductionFunctor (dec J) (hU J) ≅
    normalizedInductionFunctor (dec (leviIndex J I)) (hU (leviIndex J I)) :=
  standardInductionStagesIso i ν hInter hG hi hν hStandard hU hproj hUc J I
    (levi_isClosed i ν hStandard hG hi hν hP hproj J)
    (isLimitOfCompactSubgroups_leviUnipotent
      i ν hStandard hG hi hν hP hproj hUc J I)

end Langlands.Aubert.General.RationalPointFamily
