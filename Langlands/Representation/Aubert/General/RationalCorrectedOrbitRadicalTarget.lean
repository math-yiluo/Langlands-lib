import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets

/-! # Radical-intersection targets for surviving corrected Aubert orbits -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG u

namespace Langlands.Aubert.General.CorrectedFiltration

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G]

/-- The exact pair of subgroup-containment inputs `hS1` and `hS2` of the
conditional orbit Jacquet construction, at every actual surviving grade.
This is a proposition template, not an assertion for arbitrary families. -/
def OrbitRadicalIntersectionTarget (P M U : Finset ι → Subgroup G) (T : Subgroup G)
    [Fintype (Group.RelativeWeyl.Weyl T)] [DecidableEq (Group.RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (Group.RelativeWeyl.Weyl T)) : Prop :=
  ∀ (I : Finset ι) (j : ℕ)
    (hj : j < (Support.rankOrderedList cs.length).length)
    (m : Group.RelativeWeyl.normalizer T),
    (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
      (Support.rankOrderedElement cs.length j hj)⁻¹ →
    ∀ (K : Finset ι),
      (∀ x : G, x ∈ M I ↔ (m : G)⁻¹ * x * m ∈ M K) →
      (∀ s, K ⊆ Finset.univ \ s →
        Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
          (Support.rankOrderedElement cs.length j hj) →
        ∀ x ∈ U I,
          (m : G)⁻¹ * x * m ∈ P (Finset.univ \ s) → (m : G)⁻¹ * x * m ∈ U K) ∧
      (∀ s, K ⊆ Finset.univ \ s →
        Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
          (Support.rankOrderedElement cs.length j hj) →
        ∀ x ∈ M (Finset.univ \ s), x ∈ U K → (m : G) * x * (m : G)⁻¹ ∈ U I)

end Langlands.Aubert.General.CorrectedFiltration

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The actual rational `hS1`/`hS2` obligation under the unchanged structural
premises of the corrected graded-transition target. No proof or additional
external structural premise is supplied. -/
def RationalCorrectedOrbitRadicalIntersectionStatement : Prop :=
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
        CorrectedFiltration.OrbitRadicalIntersectionTarget
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (T := torusPoints i) (cs := cs)

end Langlands.Aubert.General.RationalPointFamily
