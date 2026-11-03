import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.General.TerminalJacquet
import Mathlib.NumberTheory.LocalField.Basic

/-! # Full-smooth Jacquet comparisons on the actual rational-point families -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

section Intrinsic

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalTerminalJacquetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Compact-limit radicals inside a closed actual Levi supply its normalization
input, without assuming an arbitrary unimodularity field. -/
theorem standardLeviUnipotent_isUnimodular
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
    (hUcLevi : ∀ (J : Finset (SimpleRoot i ν)) (K : Finset J), Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J)))
    (J : Finset (SimpleRoot i ν)) :
    letI := (hM J).locallyCompactSpace
    ∀ K : Finset J,
      IsUnimodularModulus
        ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J))
        ((hU (leviIndex J K)).preimage continuous_subtype_val) := by
  let _ := (hM J).locallyCompactSpace
  intro K
  exact isUnimodularModulus_of_isLimitOfCompactSubgroups _
    ((hU (leviIndex J K)).preimage continuous_subtype_val) (hUcLevi J K)

end Intrinsic

/-- The support-theoretic cuspidality prerequisite on the actual smooth
category. This is a separate unproved representation-theoretic assertion. -/
def RationalJacquetCuspidalStatement : Prop :=
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
      ∀ [LinearOrder (SimpleRoot i ν)],
        TerminalJacquet.JacquetCuspidalStatement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν)
          hU (rootAssociation i ν hN hZ) hM
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- The fixed-Levi equality before (**) on p.4690, as a natural isomorphism
on the full actual support category, without a finite-length premise. -/
def RationalFixedLeviComparisonStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUcLevi : ∀ (J : Finset (SimpleRoot i ν)) (K : Finset J), Jacquet.Localization.IsLimitOfCompactSubgroups
        ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
        TerminalJacquet.FixedLeviComparisonStatement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν)
          hU (standardParabolic_monotone i ν hOrder hG hi hν)
          (standardUnipotent_antitone i ν hOrder hG hi hν)
          (rootAssociation i ν hN hZ) hM
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (standardLeviUnipotent_isUnimodular i ν hU hM hUcLevi)

/-- Display (**) on the actual normalizer/full-centralizer quotient, with
root-compatible Coxeter indexing and every lift of the longest representative.
The conclusion is an unproved natural isomorphism of actual smooth functors. -/
def RationalAssociatedLeviComparisonStatement : Prop :=
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
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hUcLevi : ∀ (J : Finset (SimpleRoot i ν)) (K : Finset J), Jacquet.Localization.IsLimitOfCompactSubgroups
        ((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)]
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        ∀ (hAssociated :
          actualAssociatedLeviConjugation (torusPoints i) (levi i ν) actual),
          TerminalJacquet.AssociatedLeviComparisonStatement.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν)
            hU (standardUnipotent_isUnimodular i ν hU hUc)
            (standardParabolic_monotone i ν hOrder hG hi hν)
            (standardUnipotent_antitone i ν hOrder hG hi hν)
            (rootAssociation i ν hN hZ) hM
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
            (standardLeviUnipotent_isUnimodular i ν hU hM hUcLevi)
            (standardParabolic_univ i ν hEndpoints hG hi hν)
            (standardUnipotent_univ i ν hEndpoints hG hi hν)
            (torusPoints i) actual hAssociated

end Langlands.Aubert.General.RationalPointFamily
