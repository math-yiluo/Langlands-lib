import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets

/-! # Induced cuspidal representations and the support categories `Alg({K})` -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG uV u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Renard, proof of Théorème VI.7.2 (printed p. 183), grouped by association
classes of cuspidal Levis: the normalized induction `i^G_{L_K}(τ)` of a smooth
representation `τ` of the standard Levi `L_K` that is cuspidal inside `L_K`
lies in `Alg({K})`. The representation `τ` need not be irreducible, admissible,
finitely generated or of finite length. -/
def InducedCuspidalSupportCategoryTarget : Prop :=
  ∀ (K : Finset ι) (τ : SmoothRep.{0, uG, max uG uV} ℂ (M K)),
    IsLeviCuspidal P M U hU K (hM K) (hL K) τ →
      IsInSupportCategory P M U h hU IsAssociate K (hM K) (hL K)
        ((normalizedInductionFunctor.{uG, max uG uV} (h K) (hU K)).obj τ)

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open scoped CategoryTheory.MonObj
open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard, proof of Théorème VI.7.2, on the actual standard rational-point
families: actual normalized induction from an actual standard Levi of a smooth
representation that is cuspidal inside that Levi lies in the actual support
category of that Levi. No proof is supplied. -/
def RationalInducedCuspidalSupportCategoryStatement : Prop :=
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
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      InducedCuspidalSupportCategoryTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

end Langlands.Aubert.General.RationalPointFamily
