import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Mathlib.NumberTheory.LocalField.Basic

/-! # Nonzeroness of actual standard rational-point induction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Actual normalized induction of a nonzero smooth representation of any
standard Levi is nonzero, under the standard-cocharacter premise already
present in the rational rank-one target. -/
def RationalStandardInductionNonzeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (I : Finset (SimpleRoot i ν))
      (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) [Nontrivial σ],
      Nontrivial ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU).obj σ)

end Langlands.Aubert.General.RationalPointFamily
