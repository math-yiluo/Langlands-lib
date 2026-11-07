import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.GroupScheme.Rational.RootFiniteness

/-! The actual compact-induction-to-universal-tensor comparison of VI.4.1. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Comparison

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalProgeneratorComparisonStatementPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Existence of a complex-linear equivariant isomorphism between the actual
full-restriction compact induction and the concrete universal tensor. -/
def HasRationalUniversalProgeneratorComparison
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) : Prop :=
  Nonempty (rationalNormKernelCompactInduction G π ≅
    rationalUniversalTensorSmoothRep G π)

end Comparison

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The comparison in the alternative-progenerator remark of VI.4.1, under
irreducible cuspidality for every proper actual standard parabolic. -/
def RationalUniversalProgeneratorComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        HasRationalUniversalProgeneratorComparison G π

end Langlands.CuspidalSupport
