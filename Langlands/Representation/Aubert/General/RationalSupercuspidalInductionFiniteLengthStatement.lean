import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.SupportCategory
import Mathlib.NumberTheory.LocalField.Basic

/-! # Finite-length target for actual supercuspidal parabolic induction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The finite-length assertion of Renard, Théorème VI.5.4, on the actual
standard rational-point families. The input carrier universe is independent
of the field/group universe. No proof or explicit length bound is supplied. -/
def RationalSupercuspidalInductionFiniteLengthStatement : Prop :=
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
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
      ∀ (I : Finset (SimpleRoot i ν)) (σ : SmoothRep.{0, u, uV} ℂ (levi i ν I)),
        σ.IsIrreducible →
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
          hU I (hM I) (hL I) σ →
        ((normalizedInductionFunctor.{u, uV} (h I) (hU I)).obj σ).HasFiniteLength

end Langlands.Aubert.General.RationalPointFamily
