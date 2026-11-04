import Langlands.Representation.Aubert.General.RationalIntersectionLeviConjugation
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly

/-! # Structural Levi criterion for a corrected filtration cell -/

noncomputable section

open Classical

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
  {CM : CoxeterMatrix B} (cs : CoxeterSystem CM W) [Fintype B] [DecidableEq B]

/-- The source simple intersection is full exactly when every source label
has a simple image in the specified target. No positivity is asserted here. -/
theorem simpleImage_inv_inter_eq_iff_mapsIntoSimple (w : W) (I J : Finset B) :
    simpleImage cs w⁻¹ J ∩ I = I ↔ MapsIntoSimple cs w I J := by
  rw [Finset.inter_eq_right]
  constructor
  · intro h a ha
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ J, w⁻¹ * cs.simple b * (w⁻¹)⁻¹ = cs.simple a := by
      simpa only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and] using h ha
    refine ⟨b, hb, ?_⟩
    rw [← hba]
    group
  · intro h a ha
    obtain ⟨b, hb, hab⟩ := h a ha
    have hba : w⁻¹ * cs.simple b * (w⁻¹)⁻¹ = cs.simple a := by
      rw [← hab]
      group
    simpa only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and] using
      (show ∃ b ∈ J, w⁻¹ * cs.simple b * (w⁻¹)⁻¹ = cs.simple a from ⟨b, hb, hba⟩)

/-- Failure of fullness makes the source intersection a proper subset. -/
theorem simpleImage_inv_inter_ssubset (w : W) (I J : Finset B)
    (h : simpleImage cs w⁻¹ J ∩ I ≠ I) :
    simpleImage cs w⁻¹ J ∩ I ⊂ I :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, h⟩

/-- The two simple-intersection indices have equal cardinality, since
conjugation is a bijection on their reflection labels. -/
theorem card_simpleImage_intersections (w : W) (I J : Finset B) :
    (simpleImage cs w⁻¹ J ∩ I).card = (simpleImage cs w I ∩ J).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (simpleConjugationEquiv cs w (simpleImage cs w⁻¹ J ∩ I)
        (simpleImage cs w I ∩ J) (mapsIntoSimple_intersections cs w I J)
        (simpleImage_inv_inter cs w I J))

end Langlands.Group.RelativeWeylIndexing

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

universe u

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- Root association cannot lower the cardinality of the simple index. -/
theorem not_rootAssociation_of_card_lt
    {I K : Finset (SimpleRoot i ν)} (hK : K.card < I.card)
    (n : RationalPoint k G.X) :
    ¬ rootAssociation i ν hN hZ I K n := by
  intro h
  have heq := rootAssociation_card_eq i ν hN hZ h
  omega

/-- No subset of a proper subset of `I` can be root-associated to `I`. -/
theorem not_rootAssociation_below_proper
    {I H K : Finset (SimpleRoot i ν)} (hH : H ⊂ I) (hK : K ⊆ H)
    (n : RationalPoint k G.X) :
    ¬ rootAssociation i ν hN hZ I K n := by
  exact not_rootAssociation_of_card_lt i ν hN hZ
    (lt_of_le_of_lt (Finset.card_le_card hK) (Finset.card_lt_card hH)) n

variable [Fintype (SimpleRoot i ν)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)

/-- A proper source intersection supplies precisely the no-associated-Levi
antecedent used by support-category Jacquet vanishing. It asserts no vanishing. -/
theorem correctedIntersection_supportExclusion
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
    (h : simpleImage cs w⁻¹ J ∩ I ≠ I) :
    ∀ (K : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
      K ⊆ simpleImage cs w⁻¹ J ∩ I →
      rootAssociation i ν hN hZ I K n →
      ¬ ∀ x : RationalPoint k G.X,
        x ∈ levi i ν K ↔
          n⁻¹ * x * n ∈ levi i ν I := by
  intro K n hK hAssoc
  exact (not_rootAssociation_below_proper i ν hN hZ
    (simpleImage_inv_inter_ssubset cs w I J h) hK n hAssoc).elim

/-- A proper source intersection also excludes every associate below the
target intersection, which is the Jacquet index in the one-cell term. -/
theorem correctedTargetIntersection_supportExclusion
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
    (h : simpleImage cs w⁻¹ J ∩ I ≠ I) :
    ∀ (K : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X),
      K ⊆ simpleImage cs w I ∩ J →
      rootAssociation i ν hN hZ I K n →
      ¬ ∀ x : RationalPoint k G.X,
        x ∈ levi i ν K ↔
          n⁻¹ * x * n ∈ levi i ν I := by
  intro K n hK hAssoc
  have hlt : (simpleImage cs w I ∩ J).card < I.card := by
    rw [← card_simpleImage_intersections cs w I J]
    exact Finset.card_lt_card (simpleImage_inv_inter_ssubset cs w I J h)
  exact (not_rootAssociation_of_card_lt i ν hN hZ
    (lt_of_le_of_lt (Finset.card_le_card hK) hlt) n hAssoc).elim

variable
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

include hLength hSimple hG hi hν hStandard in
/-- Fullness at a minimum gives the literal inverse-conjugation membership
for every specified lift of `w⁻¹`. The conjugation premise comes from `hStandard`. -/
theorem correctedLeviConjugationMembership
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hfull : simpleImage cs w⁻¹ J ∩ I = I)
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hm : QuotientGroup.mk m = w⁻¹) :
    ∀ x : RationalPoint k G.X,
      x ∈ levi i ν I ↔
        (m : RationalPoint k G.X)⁻¹ * x * (m : RationalPoint k G.X) ∈
          levi i ν (simpleImage cs w I ∩ J) := by
  have hroot :
      weylCharacterAction i hN hZ w⁻¹ '' rootSet i ν (simpleImage cs w I ∩ J) =
        rootSet i ν I := by
    simpa only [inv_inv, hfull] using
      rootSet_simpleImage_intersections i ν hN hZ cs hLength hSimple J I w⁻¹
        (isMinimal_inv cs hw)
  have hchar :
      weylAction i ((normalizerEquiv i hN).symm m) ''
          rootSet i ν (simpleImage cs w I ∩ J) =
        rootSet i ν I := by
    rw [← weylCharacterAction_point_mk i hN hZ, hm]
    exact hroot
  exact conjugationMembership_of_map_eq _
    (levi_map_conj_of_character_image i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      I (simpleImage cs w I ∩ J) ((normalizerEquiv i hN).symm m) hchar)

include hLength hSimple hG hi hν hStandard in
/-- The exact structural conclusion required by a surviving corrected grade,
conditional only on minimum-representative fullness. -/
theorem exists_correctedLevi_of_full_intersection
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hfull : simpleImage cs w⁻¹ J ∩ I = I)
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hm : QuotientGroup.mk m = w⁻¹) :
    ∃ K : Finset (SimpleRoot i ν), K ⊆ J ∧
      ∀ x : RationalPoint k G.X,
        x ∈ levi i ν I ↔
          (m : RationalPoint k G.X)⁻¹ * x * (m : RationalPoint k G.X) ∈ levi i ν K :=
  ⟨simpleImage cs w I ∩ J, Finset.inter_subset_right,
    correctedLeviConjugationMembership i ν hN hZ cs hLength hSimple hG hi hν
      hStandard I J w hw hfull m hm⟩

variable [TopologicalSpace (RationalPoint k G.X)]
  [IsTopologicalGroup (RationalPoint k G.X)]

/-- The actual continuous inverse-conjugation equivalence when the source
intersection is full; it retains the chosen lift of `w⁻¹`. -/
def correctedLeviConjugationEquiv
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hfull : simpleImage cs w⁻¹ J ∩ I = I)
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hm : QuotientGroup.mk m = w⁻¹) :
    levi i ν I ≃ₜ* levi i ν (simpleImage cs w I ∩ J) :=
  conjugationEquiv (m : RationalPoint k G.X)
    (correctedLeviConjugationMembership i ν hN hZ cs hLength hSimple hG hi hν
      hStandard I J w hw hfull m hm)

@[simp]
theorem correctedLeviConjugationEquiv_apply
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (hfull : simpleImage cs w⁻¹ J ∩ I = I)
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hm : QuotientGroup.mk m = w⁻¹) (x : levi i ν I) :
    (correctedLeviConjugationEquiv i ν hN hZ cs hLength hSimple hG hi hν hStandard
        I J w hw hfull m hm x : RationalPoint k G.X) =
      (m : RationalPoint k G.X)⁻¹ * (x : RationalPoint k G.X) *
        (m : RationalPoint k G.X) := rfl

end Langlands.Aubert.General.RationalPointFamily
