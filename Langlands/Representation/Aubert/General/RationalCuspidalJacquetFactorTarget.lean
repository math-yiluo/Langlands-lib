import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets

/-! # Actual cuspidal Jacquet-factor extraction target -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG uV u v

open CategoryTheory

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}

/-- A proposition template for the cuspidal-factor consequence of Renard
VI.5.3(ii),(iii), applied after exact Jacquet restriction to an actual
subquotient of a cuspidal induction. The same representative supplies the
association, the Levi membership comparison and the actual datum isomorphism.
This definition asserts no theorem for arbitrary subgroup families. -/
def CuspidalJacquetFactorExtractionTarget
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hM : ∀ I, IsClosed (M I : Set G))
    (hL : ∀ (I : Finset ι) (K : Finset I),
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I)))
    (IsAssociate : Finset ι → Finset ι → G → Prop) : Prop :=
  ∀ (I J : Finset ι) (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (π : SmoothRep.{0, uG, max uG uV} ℂ G)
    (τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)),
    σ.IsIrreducible → IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
    τ.IsIrreducible → IsLeviCuspidal P M U hU J (hM J) (hL J) τ →
    SmoothRep.IsSubquotient π
      ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ) →
    SmoothRep.IsSubquotient τ ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj π) →
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧ Nonempty (τ ≅ (conjugationFunctor n hn).obj σ)

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The actual rational-point cuspidal Jacquet-factor extraction target.
It is a consequence to be proved from Renard VI.5.3(ii),(iii), actual Jacquet
exactness and actual normalizer/Levi transport comparisons; no proof is
supplied. The representation π is an arbitrary smooth subquotient of the
induction, with no irreducibility or finite-length premise. -/
def RationalCuspidalJacquetFactorExtractionStatement : Prop :=
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
      CuspidalJacquetFactorExtractionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)


end Langlands.Aubert.General.RationalPointFamily
