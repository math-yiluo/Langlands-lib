import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportStatement
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy
import Langlands.Group.RelativeWeylAssociatedSubsetEquiv

/-! # Actual normalizer lifts for associated opposite conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)

/-- A scheme-normalizer lift of the actual longest representative. -/
def longestSchemeNormalizerLift [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) (J : Finset (SimpleRoot i ν)) :
    normalizerPoints i :=
  Classical.choose (QuotientGroup.mk_surjective (longestRep cs J))

@[simp]
theorem longestSchemeNormalizerLift_mk
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) (J : Finset (SimpleRoot i ν)) :
    QuotientGroup.mk (longestSchemeNormalizerLift i ν cs J) = longestRep cs J :=
  Classical.choose_spec (QuotientGroup.mk_surjective (longestRep cs J))

/-- The inverse of a scheme-normalizer point lies in the actual point normalizer.
Only the elementary inclusion of normalizers is needed. -/
def inversePointNormalizer (n : normalizerPoints i) :
    Group.RelativeWeyl.normalizer (torusPoints i) :=
  ⟨(n : RationalPoint k G.X)⁻¹,
    normalizerPoints_le_pointNormalizer i ((normalizerPoints i).inv_mem n.property)⟩

omit [IsAffineHom G.X.hom] in
@[simp]
theorem inversePointNormalizer_coe (n : normalizerPoints i) :
    (inversePointNormalizer i n : RationalPoint k G.X) = (n : RationalPoint k G.X)⁻¹ :=
  rfl

variable [Mono i.hom.hom.left]
  [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup i))

/-- The associated subset is the literal inverse longest-element image of the
actual simple characters, for a scheme relative-Weyl realization. -/
theorem rootSet_associatedSubset_of_schemeCoxeter
    (hT : IsSplitTorus T.toGrp) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Finset (SimpleRoot i ν)) :
    rootSet i ν (associatedSubset cs J) =
      schemeWeylCharacterAction i (longestRep cs J)⁻¹ '' rootSet i ν J := by
  classical
  have hmin : IsMinimal cs ∅ J (longestRep cs J)⁻¹ :=
    isMinimal_inv cs ((mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J))
  have hpos (a : SimpleRoot i ν) (ha : a ∈ J) :
      schemeWeylCharacterAction i (longestRep cs J)⁻¹ a.val ∈ positiveRelativeRoots i ν :=
    (hcs.2.2.1 _ a).mp (((minimalityLengthCriterion_proof cs ∅ J _).mp hmin).2 a ha)
  ext α
  constructor
  · rintro ⟨b, hb, rfl⟩
    change b ∈ simpleImage cs (longestRep cs J)⁻¹ J at hb
    simp only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨a.val, ⟨a, ha, rfl⟩, (hcs.conj_simple_iff hT _ a b (hpos a ha)).mp hab⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, _, hab⟩ := (associatedSubsetLaws_proof cs J).1 a ha
    have he := (hcs.conj_simple_iff hT _ a b (hpos a ha)).mp hab
    refine ⟨b, ?_, he.symm⟩
    change b ∈ simpleImage cs (longestRep cs J)⁻¹ J
    simp only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, hab⟩

/-- The separate all-test Levi assertion yields the actual associated Levi
image for every scheme longest lift, without a point-quotient comparison. -/
theorem associatedLevi_map_conj_of_schemeCoxeter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (levi i ν (associatedSubset cs J)).map
        (MulAut.conj (n : RationalPoint k G.X) : _ →* _) = levi i ν J := by
  apply levi_map_conj_of_character_image i ν hG hi hν hConj
  rw [← schemeWeylCharacterAction_mk, hn,
    rootSet_associatedSubset_of_schemeCoxeter i ν cs hi.isSplitSubtorus.1 hcs,
    Set.image_image]
  have hcancel :
      (fun α => schemeWeylCharacterAction i (longestRep cs J)
        (schemeWeylCharacterAction i (longestRep cs J)⁻¹ α)) = id := by
    funext α
    change (schemeWeylCharacterAction i (longestRep cs J) *
      schemeWeylCharacterAction i (longestRep cs J)⁻¹) α = α
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hcancel, Set.image_id]

set_option maxHeartbeats 800000 in
/-- The same inverse longest lift provides all three membership comparisons
needed by actual normalized induction and Jacquet conjugation. -/
theorem associatedOpposite_mem_of_structural
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (hOpp : IsStandardAssociatedOppositeTransport i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ)
    (x : RationalPoint k G.X) :
    (x ∈ parabolic i ν (associatedSubset cs J) ↔
      (inversePointNormalizer i n : RationalPoint k G.X)⁻¹ * x *
        (inversePointNormalizer i n : RationalPoint k G.X) ∈ oppositeParabolic i ζ) ∧
    (x ∈ levi i ν (associatedSubset cs J) ↔
      (inversePointNormalizer i n : RationalPoint k G.X)⁻¹ * x *
        (inversePointNormalizer i n : RationalPoint k G.X) ∈ levi i ν J) ∧
    (x ∈ unipotent i ν (associatedSubset cs J) ↔
      (inversePointNormalizer i n : RationalPoint k G.X)⁻¹ * x *
        (inversePointNormalizer i n : RationalPoint k G.X) ∈ oppositeUnipotent i ζ) := by
  obtain ⟨hP, hU⟩ :=
    IsStandardAssociatedOppositeTransport.mem_rationalPoints i ν (cs := cs)
      hOpp J n hn ζ hζ x
  have hM := (conjugationMembership_of_map_eq (n : RationalPoint k G.X)
    (associatedLevi_map_conj_of_schemeCoxeter i ν cs hG hi hν hConj hcs J n hn)
    ((n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹)).symm
  refine ⟨?_, ?_, ?_⟩
  · simpa only [inversePointNormalizer_coe, inv_inv, parabolic, standardParabolicPoints,
      SubgroupFunctor.rationalPoints, oppositeParabolic, Dynamic.oppositeCocharacter,
      Dynamic.inverseCocharacter] using hP
  · simpa only [inversePointNormalizer_coe, inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel, inv_mul_cancel, mul_one] using hM
  · simpa only [inversePointNormalizer_coe, inv_inv, unipotent, standardUnipotentPoints,
      SubgroupFunctor.rationalPoints, oppositeUnipotent, Dynamic.oppositeCocharacter,
      Dynamic.inverseCocharacter] using hU

end Langlands.Aubert.General.RationalPointFamily
