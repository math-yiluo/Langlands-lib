import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Mathlib.NumberTheory.LocalField.Basic
import Langlands.Representation.Smooth.IrreducibleRealization
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! # Cuspidal eigenvalue on the actual rational-point group -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Aubert Theorem 1.7(4) on the canonical rational-point topology. This declares a target; no instance is proved. -/
def RationalCuspidalEigenvalueStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
        (hA : A.IsIrreducible),
        (∀ I : Finset (SimpleRoot i ν), I ≠ Finset.univ →
          Limits.IsZero ((jacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν I) (hU I)).obj A)) →
        rationalAlternatingOperator.{u, v}
            i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots
            (FiniteLengthGrothendieckGroup.ofRepresentation A
              (hasFiniteLength_of_isIrreducible hA)) =
          ((-1 : ℤ) ^ Fintype.card (SimpleRoot i ν)) •
            FiniteLengthGrothendieckGroup.ofRepresentation A
              (hasFiniteLength_of_isIrreducible hA)

end Langlands.Aubert.General.RationalPointFamily
