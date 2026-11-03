import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.CorrectedTheorem36
import Mathlib.NumberTheory.LocalField.Basic

/-! # Corrected Theorem 3.6 on the actual rational-point smooth category -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The corrected theorem for every smooth object of the actual support
category. Finite length is not a premise, and the terminal cokernel is retained. -/
def RationalCorrectedTheorem36Statement : Prop :=
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
      (hOrder : StandardParabolicOrderStatement.{u})
      (hEndpoints : StandardParabolicEndpointsStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν)),
        CorrectedTheorem36Statement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν)
          hU (standardUnipotent_isUnimodular i ν hU hUc)
          (standardParabolic_monotone i ν hOrder hG hi hν)
          (standardUnipotent_antitone i ν hOrder hG hi hν)
          (rootAssociation i ν hN hZ)
          (standardParabolic_univ i ν hEndpoints hG hi hν)
          (standardUnipotent_univ i ν hEndpoints hG hi hν)
          I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I)

section IntrinsicLaws

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)] [LinearOrder (SimpleRoot i ν)]
  (hStandard : StandardCocharacterStatement.{u})
  (hOrder : StandardParabolicOrderStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

/-- The final arrow is onto the actual retained quotient. -/
theorem rationalTerminalProjection_surjective
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :
    Function.Surjective
      (rationalTerminalProjection i ν hStandard hOrder hG hi hν hU hUc E q) :=
  StandardComplex.terminalProjection_surjective.{u, u, max (u + 1) v}
    _ _ _ _ _ _ _ _ E q

/-- The final kernel is its actual incoming image, without an earlier exactness
or a terminal-vanishing hypothesis. -/
theorem rationalTerminalProjection_ker
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :
    LinearMap.ker
        (rationalTerminalProjection i ν hStandard hOrder hG hi hν hU hUc E q).toLinearMap =
      rationalBoundary i ν hStandard hOrder hG hi hν hU hUc E q :=
  StandardComplex.terminalProjection_ker.{u, u, max (u + 1) v}
    _ _ _ _ _ _ _ _ E q

end IntrinsicLaws

end Langlands.Aubert.General.RationalPointFamily
