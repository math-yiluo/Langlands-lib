import Langlands.Representation.Aubert.General.MaximalRootAssociation
import Langlands.Group.RelativeWeylAssociatedSubsetProof
import Langlands.Group.RelativeWeylSolomonProof

/-! # Weyl classes of maximal actual root associations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

private theorem maximal_subset_eq {B : Type*} [Fintype B] [DecidableEq B]
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
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

private theorem rootMaps_of_image
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
  [Fintype (Weyl i)] {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)

/-- Actual association records both its Weyl class and its target subset. -/
def MaximalRootAssociationClassDichotomy : Prop :=
  ∀ (J K : Finset (SimpleRoot i ν)) (w : Weyl i),
    IsMaximalStandard J →
    weylCharacterAction i hN hZ w '' rootSet i ν J = rootSet i ν K →
      (w = 1 ∧ K = J) ∨
        (w = (longestRep actual J)⁻¹ ∧ K = associatedSubset actual J)

variable
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hMin : minimalityLengthCriterion actual)

include hLength hSimple hMin in
/-- The root-sign comparisons determine every class carrying a maximal
standard root subset onto another standard root subset. -/
theorem rootImage_class_eq_one_or_eq_inv_longest
    {J K : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hJ : IsMaximalStandard J)
    (himage : weylCharacterAction i hN hZ w '' rootSet i ν J = rootSet i ν K) :
    (w = 1 ∧ K = J) ∨
      (w = (longestRep actual J)⁻¹ ∧ K = associatedSubset actual J) := by
  classical
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective w
  have hJK : rootAssociation i ν hN hZ J K n.val := by
    refine ⟨n.property, ?_⟩
    change weylCharacterAction i hN hZ (QuotientGroup.mk n) '' rootSet i ν J = _
    rwa [hn]
  have hK := rootAssociation_isMaximalStandard i ν hN hZ hJK hJ
  by_cases hw : w = 1
  · refine Or.inl ⟨hw, ?_⟩
    apply rootSet_injective i ν
    simpa [hw] using himage.symm
  · have hinvimage :
        weylCharacterAction i hN hZ w⁻¹ '' rootSet i ν K = rootSet i ν J := by
      rw [map_inv, ← himage]
      ext α
      simp
    have hmap := rootMaps_of_image i ν hN hZ w J K himage
    have hinvmap := rootMaps_of_image i ν hN hZ w⁻¹ K J hinvimage
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
    have hset := maximal_subset_eq hK hsubset hproper
    have hreflection : MapsIntoSimple actual w⁻¹ (positiveSimpleSet actual w⁻¹) J := by
      rw [← hset]
      exact (rootMapsIntoSimple_iff_of_positive i ν hN hZ actual hSimple
        w⁻¹ K J hinvpos).mp hinvmap
    have hlong : w⁻¹ = longestRep actual J :=
      ((longestSurvivor_proof actual) J w⁻¹ hinvminimal).mp hreflection
    have hwlong : w = (longestRep actual J)⁻¹ := by
      simpa only [inv_inv] using congrArg Inv.inv hlong
    refine Or.inr ⟨hwlong, ?_⟩
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

include hLength hSimple hMin in
/-- The class dichotomy is a conclusion of the original comparison hypotheses. -/
theorem maximalRootAssociationClassDichotomy_of_rootSignComparisons :
    MaximalRootAssociationClassDichotomy i ν hN hZ actual := by
  intro J K w hJ himage
  exact rootImage_class_eq_one_or_eq_inv_longest i ν hN hZ actual
    hLength hSimple hMin hJ himage

omit [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)] in
/-- On equally large finite subsets, mapping all actual simple roots into
the target already gives equality of the root images. -/
theorem rootImage_eq_of_mapsIntoSimple_of_card
    {J K : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hmap : RootMapsIntoSimple i ν hN hZ w J K) (hcard : J.card = K.card) :
    weylCharacterAction i hN hZ w '' rootSet i ν J = rootSet i ν K := by
  classical
  let f : J → K := fun a =>
    ⟨Classical.choose (hmap a.val a.property),
      (Classical.choose_spec (hmap a.val a.property)).1⟩
  have hf (a : J) :
      weylCharacterAction i hN hZ w a.val.val = (f a).val.val :=
    (Classical.choose_spec (hmap a.val a.property)).2
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply (weylCharacterAction i hN hZ w).injective
    exact (hf a).trans ((congrArg (fun x : K => x.val.val) hab).trans (hf b).symm)
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa using hcard⟩).2
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, hab⟩ := hmap a ha
    exact ⟨b, hb, hab.symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := hsurj ⟨b, hb⟩
    exact ⟨a.val.val, ⟨a.val, a.property, rfl⟩,
      (hf a).trans (congrArg (fun x : K => x.val.val) ha)⟩

include hLength hSimple hMin in
omit [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)] in
/-- A full source intersection at a minimal representative gives actual
root association when source and target have equal cardinality. -/
theorem rootImage_eq_of_full_intersection
    {J K : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hw : IsMinimal actual K J w)
    (hfull : intersectionSubset actual K J w = J)
    (hcard : J.card = K.card) :
    weylCharacterAction i hN hZ w '' rootSet i ν J = rootSet i ν K := by
  classical
  apply rootImage_eq_of_mapsIntoSimple_of_card i ν hN hZ _ hcard
  have hpos : ∀ a ∈ J,
      weylCharacterAction i hN hZ w a.val ∈ positiveRelativeRoots i ν := by
    intro a ha
    exact (hLength w a).mp (((hMin K J w).mp hw).2 a ha)
  apply (rootMapsIntoSimple_iff_of_positive i ν hN hZ actual hSimple w J K hpos).mpr
  intro a ha
  have hmem : a ∈ intersectionSubset actual K J w := hfull.symm ▸ ha
  have hc : w * actual.simple a * w⁻¹ ∈ standardSubgroup actual K :=
    (Finset.mem_filter.mp hmem).2
  exact exists_conj_simple_eq_of_isMinimal actual hw ha hc

omit [Mono i.hom.hom.left] [Fintype (SimpleRoot i ν)]
  [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)] in
private theorem intersectionSubset_eq_of_maps
    {J K : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hmap : MapsIntoSimple actual w J K) :
    intersectionSubset actual K J w = J := by
  classical
  apply le_antisymm (intersectionSubset_subset actual K J w)
  intro a ha
  obtain ⟨b, hb, hab⟩ := hmap a ha
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_⟩
  rw [hab]
  exact simple_mem_standardSubgroup actual hb

include hLength hSimple hMin in
/-- For a maximal subset different from its associate, only the identity
minimal representative has full source intersection with itself. -/
theorem full_self_intersection_iff_eq_one
    {J : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hJ : IsMaximalStandard J) (hne : J ≠ associatedSubset actual J)
    (hw : IsMinimal actual J J w) :
    intersectionSubset actual J J w = J ↔ w = 1 := by
  constructor
  · intro hfull
    have himage := rootImage_eq_of_full_intersection i ν hN hZ actual
      hLength hSimple hMin hw hfull rfl
    rcases rootImage_class_eq_one_or_eq_inv_longest i ν hN hZ actual
      hLength hSimple hMin hJ himage with ⟨hw, -⟩ | ⟨-, hK⟩
    · exact hw
    · exact (hne hK).elim
  · rintro rfl
    apply intersectionSubset_eq_of_maps i ν actual
    intro a ha
    exact ⟨a, ha, by simp⟩

include hLength hSimple hMin in
/-- For a maximal subset different from its associate, only the inverse
longest representative has full source intersection with that associate. -/
theorem full_associated_intersection_iff_eq_inv_longest
    {J : Finset (SimpleRoot i ν)} {w : Weyl i}
    (hJ : IsMaximalStandard J) (hne : J ≠ associatedSubset actual J)
    (hw : IsMinimal actual (associatedSubset actual J) J w) :
    intersectionSubset actual (associatedSubset actual J) J w = J ↔
      w = (longestRep actual J)⁻¹ := by
  classical
  constructor
  · intro hfull
    have himage := rootImage_eq_of_full_intersection i ν hN hZ actual
      hLength hSimple hMin hw hfull (associatedSubsetLaws_proof actual J).2.1.symm
    rcases rootImage_class_eq_one_or_eq_inv_longest i ν hN hZ actual
      hLength hSimple hMin hJ himage with ⟨-, hK⟩ | ⟨hw, -⟩
    · exact (hne hK.symm).elim
    · exact hw
  · rintro rfl
    apply intersectionSubset_eq_of_maps i ν actual
    intro a ha
    obtain ⟨b, -, hab⟩ := (associatedSubsetLaws_proof actual J).1 a ha
    refine ⟨b, ?_, hab⟩
    simp only [associatedSubset, simpleImage, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, hab⟩

end Langlands.Aubert.General.RationalPointFamily
