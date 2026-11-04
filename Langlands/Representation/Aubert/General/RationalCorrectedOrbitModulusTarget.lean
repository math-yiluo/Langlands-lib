import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets

/-! # Squared intersection-modulus target for corrected Aubert orbits -/

noncomputable section

open scoped NNReal

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG u

namespace Langlands.Aubert.General.CorrectedFiltration

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The exact squared intersection-modulus input `hD07` of the conditional
orbit Jacquet construction, with its actual closed subgroup and normalizer
characters. This is a proposition template, not a theorem for all families. -/
def OrbitSquaredModulusTarget (P M U : Finset ι → Subgroup G)
    (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
    (hclosed : ∀ J, IsClosed (U J : Set G)) (T : Subgroup G)
    [Fintype (Group.RelativeWeyl.Weyl T)] [DecidableEq (Group.RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (Group.RelativeWeyl.Weyl T)) : Prop :=
  ∀ (I : Finset ι) (j : ℕ)
    (hj : j < (Support.rankOrderedList cs.length).length)
    (m : Group.RelativeWeyl.normalizer T),
    (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
      (Support.rankOrderedElement cs.length j hj)⁻¹ →
    ∀ (K : Finset ι) (hK : ∀ x : G, x ∈ M I ↔ (m : G)⁻¹ * x * m ∈ M K)
      (l : M I),
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I)
          (h I).levi_le_normalizer l : ℝ≥0) *
        (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K)
          (h K).levi_le_normalizer (conjugationEquiv (m : G) hK l) : ℝ≥0) =
      (HaarModulus.closedRestrictCharacter
          (orbitUnipotentIntersection (U I) (U K) (m : G))
          (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) (m : G)) (M I)
          (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) (m : G) hK)
          l : ℝ≥0) ^ 2

end Langlands.Aubert.General.CorrectedFiltration

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The actual rational squared intersection-modulus obligation under the
unchanged structural premises of the corrected graded-transition target.
No proof or additional external structural premise is supplied. -/
def RationalCorrectedOrbitSquaredModulusStatement : Prop :=
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
      (_hOrder : StandardParabolicOrderStatement.{u})
      (_hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
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
        CorrectedFiltration.OrbitSquaredModulusTarget
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν)
          (hclosed := hU) (T := torusPoints i) (cs := cs)

end Langlands.Aubert.General.RationalPointFamily
