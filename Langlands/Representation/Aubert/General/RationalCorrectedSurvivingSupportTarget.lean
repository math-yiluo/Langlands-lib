import Langlands.Representation.Aubert.General.CorrectedGradedInterface
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets

/-! # Fixed-order support target for the corrected Aubert filtration -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG u v

namespace Langlands.Aubert.General.CorrectedFiltration

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The exact support input of the conditional graded-transition assembly,
for the implemented decreasing-length order and its two-sided cores.
This is only a proposition template, with no assertion for arbitrary families. -/
def SurvivingSupportTarget (P : Finset ι → Subgroup G) (T : Subgroup G)
    [Fintype (Group.RelativeWeyl.Weyl T)] [DecidableEq (Group.RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (Group.RelativeWeyl.Weyl T)) : Prop :=
  ∀ (I s : Finset ι) (j : ℕ)
    (hj : j < (Support.rankOrderedList cs.length).length)
    (m : Group.RelativeWeyl.normalizer T),
    (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
      (Support.rankOrderedElement cs.length j hj)⁻¹ →
    Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
      (Support.rankOrderedElement cs.length j hj) →
    SurvivingSupportHypotheses P T cs I s j (m : G)

end Langlands.Aubert.General.CorrectedFiltration

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The exact rational fixed-order support obligation for the existing
corrected graded-transition target, with its same structural premises.
The conclusion concerns actual subsets of the rational-point group and
supplies both open supports, parabolic invariance and their single-cell
difference. It supplies no proof or additional external-input hypothesis. -/
def RationalCorrectedSurvivingSupportStatement : Prop :=
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
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{u})
      (_hOrder : StandardParabolicOrderStatement.{u})
      (_hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (_hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (_hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
      letI : DecidableEq (Weyl i) := Classical.decEq _
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        CorrectedFiltration.SurvivingSupportTarget
          (P := parabolic i ν) (T := torusPoints i) (cs := cs)

end Langlands.Aubert.General.RationalPointFamily
