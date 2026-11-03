import Langlands.Representation.Aubert.General.RootAssociationComposition
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Langlands.Group.RelativeWeylLongestSurvivorProof

/-! # The two possible standard associates of a maximal root subset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

private theorem maximalStandard_subset_eq {B : Type*} [Fintype B] [DecidableEq B]
    {I J : Finset B} (hI : IsMaximalStandard I) (hIJ : I ⊆ J)
    (hJ : J ≠ Finset.univ) : I = J := by
  obtain ⟨a, rfl⟩ := hI
  apply Finset.eq_of_subset_of_card_le hIJ
  have hlt : J.card < (Finset.univ : Finset B).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ J, hJ⟩)
  rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
  omega

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

private theorem rootMapsIntoSimple_of_image_eq
    (w : Weyl i) (I J : Finset (SimpleRoot i ν))
    (h : weylCharacterAction i hN hZ w '' rootSet i ν I = rootSet i ν J) :
    RootMapsIntoSimple i ν hN hZ w I J := by
  intro a ha
  have hb : weylCharacterAction i hN hZ w a.val ∈ rootSet i ν J := by
    rw [← h]
    exact ⟨a.val, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨b, hb, heq⟩ := hb
  exact ⟨b, hb, heq.symm⟩

variable [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]

/-- Actual root association preserves maximality of standard subsets. -/
theorem rootAssociation_isMaximalStandard {J K : Finset (SimpleRoot i ν)}
    {n : RationalPoint k G.X} (hJK : rootAssociation i ν hN hZ J K n)
    (hJ : IsMaximalStandard J) : IsMaximalStandard K := by
  classical
  obtain ⟨a, hJa⟩ := hJ
  have hJproper : J ≠ Finset.univ := by
    rw [hJa]
    exact Finset.erase_ne_self.mpr (Finset.mem_univ a)
  have hKproper := rootAssociation_ne_univ i ν hN hZ hJK hJproper
  obtain ⟨b, hb⟩ : ∃ b : SimpleRoot i ν, b ∉ K := by
    by_contra h
    push Not at h
    exact hKproper (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨b, Finset.eq_of_subset_of_card_le
    (Finset.subset_erase.mpr ⟨Finset.subset_univ K, hb⟩) ?_⟩
  have hcard := rootAssociation_card_eq i ν hN hZ hJK
  rw [hJa, Finset.card_erase_of_mem (Finset.mem_univ a)] at hcard
  rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
  omega

variable [Fintype (Weyl i)] {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)

/-- The finite-root restriction on actual associates of maximal standard
subsets, with the source's specified associated subset. -/
def MaximalRootAssociationDichotomy : Prop :=
  ∀ (J K : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
    IsMaximalStandard J → rootAssociation i ν hN hZ J K n →
      K = J ∨ K = associatedSubset actual J

/-- With the target's root-sign comparisons, an actual associate of a maximal
standard subset is either itself or the specified associated subset. -/
theorem rootAssociation_eq_or_eq_associatedSubset
    (hLength : RootLengthComparison i ν hN hZ actual)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
    (hMin : minimalityLengthCriterion actual)
    {J K : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hJ : IsMaximalStandard J) (hJK : rootAssociation i ν hN hZ J K n) :
    K = J ∨ K = associatedSubset actual J := by
  classical
  have hK := rootAssociation_isMaximalStandard i ν hN hZ hJK hJ
  have hKJ := rootAssociation_inv i ν hN hZ hJK
  obtain ⟨hn, himage⟩ := hJK
  let w : Weyl i := QuotientGroup.mk
    (⟨n, hn⟩ : Group.RelativeWeyl.normalizer (torusPoints i))
  change weylCharacterAction i hN hZ w '' rootSet i ν J = rootSet i ν K at himage
  by_cases hw : w = 1
  · left
    apply rootSet_injective i ν
    simpa [hw] using himage.symm
  · right
    obtain ⟨hninv, hinvimage⟩ := hKJ
    change weylCharacterAction i hN hZ
      (QuotientGroup.mk (⟨n, hn⟩ : Group.RelativeWeyl.normalizer (torusPoints i))⁻¹) ''
        rootSet i ν K = rootSet i ν J at hinvimage
    rw [QuotientGroup.mk_inv] at hinvimage
    change weylCharacterAction i hN hZ w⁻¹ '' rootSet i ν K = rootSet i ν J at hinvimage
    have hmap := rootMapsIntoSimple_of_image_eq i ν hN hZ w J K himage
    have hinvmap := rootMapsIntoSimple_of_image_eq i ν hN hZ w⁻¹ K J hinvimage
    have hpos : ∀ a ∈ J,
        weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν := by
      intro a ha
      obtain ⟨b, _, hab⟩ := hmap a ha
      rw [hab]
      exact simpleRelativeRoots_subset_positive i ν b.property
    have hinvpos : ∀ a ∈ K,
        weylCharacterAction i hN hZ w⁻¹ a.val ∈ positiveRelativeRoots i ν := by
      intro a ha
      obtain ⟨b, _, hab⟩ := hinvmap a ha
      rw [hab]
      exact simpleRelativeRoots_subset_positive i ν b.property
    have hminimal : IsMinimal actual ∅ J w := (hMin ∅ J w).mpr
      ⟨by simp, fun a ha => (hLength w a).mpr (hpos a ha)⟩
    have hinvminimal : IsMinimal actual J ∅ w⁻¹ := isMinimal_inv actual hminimal
    have hsubset : K ⊆ positiveSimpleSet actual w⁻¹ := by
      intro a ha
      exact (mem_positiveSimpleSet actual w⁻¹ a).mpr
        ((hLength w⁻¹ a).mpr (hinvpos a ha))
    have hproper : positiveSimpleSet actual w⁻¹ ≠ Finset.univ := by
      obtain ⟨a, ha⟩ := actual.exists_rightDescent_of_ne_one (inv_ne_one.mpr hw)
      have hd := actual.isRightDescent_iff.mp ha
      intro hfull
      have hup := (mem_positiveSimpleSet actual w⁻¹ a).mp
        (hfull.symm ▸ Finset.mem_univ a)
      omega
    have hset := maximalStandard_subset_eq hK hsubset hproper
    have hreflection : MapsIntoSimple actual w⁻¹ (positiveSimpleSet actual w⁻¹) J := by
      rw [← hset]
      exact (rootMapsIntoSimple_iff_of_positive i ν hN hZ actual hSimple
        w⁻¹ K J hinvpos).mp hinvmap
    have hlong : w⁻¹ = longestRep actual J :=
      ((longestSurvivor_proof actual) J w⁻¹ hinvminimal).mp hreflection
    have hwlong : w = (longestRep actual J)⁻¹ := by
      simpa only [inv_inv] using congrArg Inv.inv hlong
    apply rootSet_injective i ν
    calc
      rootSet i ν K = weylCharacterAction i hN hZ w '' rootSet i ν J := himage.symm
      _ = rootSet i ν (rootSimpleImage i ν hN hZ w J) :=
        (rootSet_rootSimpleImage_of_mapsIntoSimple i ν hN hZ w J K hmap).symm
      _ = rootSet i ν (simpleImage actual w J) := congrArg (rootSet i ν)
        (rootSimpleImage_eq_simpleImage_of_positive i ν hN hZ actual hSimple w J hpos)
      _ = rootSet i ν (associatedSubset actual J) := by
        rw [hwlong]
        rfl

/-- The finite-root dichotomy follows from a subset of the original rational
rank-one target's explicit Coxeter comparison hypotheses. -/
theorem maximalRootAssociationDichotomy_of_rootSignComparisons
    (hLength : RootLengthComparison i ν hN hZ actual)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
    (hMin : minimalityLengthCriterion actual) :
    MaximalRootAssociationDichotomy i ν hN hZ actual := by
  intro J K n hJ hJK
  exact rootAssociation_eq_or_eq_associatedSubset i ν hN hZ actual
    hLength hSimple hMin hJ hJK

end Langlands.Aubert.General.RationalPointFamily
