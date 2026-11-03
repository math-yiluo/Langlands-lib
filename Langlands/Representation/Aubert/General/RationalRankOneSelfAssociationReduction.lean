import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly

/-! # Reduction of rational rank-one self-association to the subset equality -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep Langlands.Group

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {B : Type uI} [Fintype B] [DecidableEq B]
variable (P M U : Finset B → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hLevi : ∀ (J : Finset B) (I : Finset J), IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))
  (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
  {C : CoxeterMatrix B} (actual : RelativeWeylIndexing.ActualCoxeterSystem T C)

/-- The representation-theoretic subset equality in rank-one self-association,
without its actual subgroup-normalization consequence. -/
def rankOneAssociatedSubsetEquality : Prop :=
  ∀ (J : Finset B), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      RelativeWeylIndexing.associatedSubset actual J = J

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [DecidableEq B] in
/-- Actual associated-Levi conjugation upgrades the subset equality to
normalization by every specified longest-representative lift. -/
theorem longestLift_normalizes_of_associatedSubset_eq
    (hAssociated : RelativeWeylIndexing.actualAssociatedLeviConjugation T M actual)
    (J : Finset B) (hself : RelativeWeylIndexing.associatedSubset actual J = J)
    (n : RelativeWeyl.normalizer T)
    (hn : QuotientGroup.mk n = RelativeWeylIndexing.longestRep actual J) :
    ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J := by
  have hImage := hAssociated J n hn
  rw [hself] at hImage
  have hmem := conjugationMembership_of_map_eq (n : G) hImage
  intro x
  simpa [mul_assoc] using (hmem ((n : G) * x * (n : G)⁻¹)).symm

/-- For actual associated-Levi conjugation, the full rank-one target is
equivalent to its representation-theoretic subset equality. -/
theorem rankOneSelfAssociation_iff_associatedSubsetEquality
    (hAssociated : RelativeWeylIndexing.actualAssociatedLeviConjugation T M actual) :
    rankOneSelfAssociation.{uI, uG, uV} P M U h hU hM hLevi T actual ↔
      rankOneAssociatedSubsetEquality.{uI, uG, uV} P M U h hU hM hLevi T actual := by
  constructor
  · intro hfull J hJ σ hσ hcusp hred
    exact (hfull J hJ σ hσ hcusp hred).1
  · intro heq J hJ σ hσ hcusp hred
    have hself := heq J hJ σ hσ hcusp hred
    exact ⟨hself, longestLift_normalizes_of_associatedSubset_eq M T actual
      hAssociated J hself⟩

end Generic

namespace RationalPointFamily

universe u v

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The exact rational rank-one representation-theoretic equality, with the
same universes, actual families and visible premises as the full target. -/
def RationalRankOneAssociatedSubsetEqualityStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        rankOneAssociatedSubsetEquality.{u, u, max (u + 1) v}
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) (hU := hU)
          (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (T := torusPoints i) (actual := actual)

/-- The full rational target implies its subset-equality part. -/
theorem rationalRankOneAssociatedSubsetEquality_of_selfAssociation
    (hfull : RationalRankOneSelfAssociationStatement.{u, v}) :
    RationalRankOneAssociatedSubsetEqualityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hσ hcusp hred
  exact (hfull k G hG T i hi ν hν hStandard hInter hRoots hU hM
    hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hσ hcusp hred).1

/-- The original standard-cocharacter premise supplies actual associated-Levi
conjugation, so the subset equality alone suffices for the full rational target. -/
theorem rationalRankOneSelfAssociation_of_associatedSubsetEquality
    (heq : RationalRankOneAssociatedSubsetEqualityStatement.{u, v}) :
    RationalRankOneSelfAssociationStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc
  apply (rankOneSelfAssociation_iff_associatedSubsetEquality
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (torusPoints i) actual
    (associatedLeviConjugation_of_standard i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      hN hZ actual hLength hSimple hMin hAssoc)).2
  exact heq k G hG T i hi ν hν hStandard hInter hRoots hU hM
    hN hZ C actual hLength hSimple hIdent hMin hAssoc

/-- At the full rational scope, actual normalization is a consequence of the
original structural premises and the representation-theoretic subset equality. -/
theorem rationalRankOneSelfAssociation_iff_associatedSubsetEquality :
    RationalRankOneSelfAssociationStatement.{u, v} ↔
      RationalRankOneAssociatedSubsetEqualityStatement.{u, v} :=
  ⟨rationalRankOneAssociatedSubsetEquality_of_selfAssociation,
    rationalRankOneSelfAssociation_of_associatedSubsetEquality⟩

end RationalPointFamily
end Langlands.Aubert.General
