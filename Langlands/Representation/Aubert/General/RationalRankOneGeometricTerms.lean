import Langlands.Representation.Aubert.General.RationalGeometricLiftComparison
import Langlands.Representation.Aubert.General.RankOneLongestLiftNormalization
import Langlands.Group.RelativeWeylCoatomSurvivors

/-! # Surviving geometric terms for a self-associated maximal Levi -/

noncomputable section

universe uB uW u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Group.RelativeWeylIndexing

variable {B : Type uB} {W : Type uW} [Group W]
  {C : CoxeterMatrix B} (cs : CoxeterSystem C W)

/-- Conjugation of simple reflections injects the source labels into the target. -/
theorem card_le_of_mapsIntoSimple {I J : Finset B} {w : W}
    (hmap : MapsIntoSimple cs w I J) : I.card ≤ J.card := by
  let f : I → J := fun a =>
    ⟨Classical.choose (hmap a.val a.property),
      (Classical.choose_spec (hmap a.val a.property)).1⟩
  have hf (a : I) :
      w * cs.simple a.val * w⁻¹ = cs.simple (f a).val :=
    (Classical.choose_spec (hmap a.val a.property)).2
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply simple_injective cs
    apply mul_left_cancel (a := w)
    apply mul_right_cancel (b := w⁻¹)
    exact (hf a).trans ((congrArg (fun x : J => cs.simple x.val) hab).trans (hf b).symm)
  simpa using Fintype.card_le_of_injective f hinj

/-- For a coatom source and any proper target, fullness leaves only the two
canonical source/representative pairs. -/
theorem coatom_fullIntersection_classification_of_proper [Fintype B] [DecidableEq B]
    [Fintype W]
    (b : B) {I : Finset B} {w : W} (hI : I ≠ Finset.univ)
    (hw : IsMinimal cs I (Finset.univ.erase b) w)
    (hfull : intersectionSubset cs I (Finset.univ.erase b) w = Finset.univ.erase b) :
    (I = Finset.univ.erase b ∧ w = 1) ∨
      (I = associatedSubset cs (Finset.univ.erase b) ∧
        w = (longestRep cs (Finset.univ.erase b))⁻¹) := by
  have hm := (intersectionSubset_eq_source_iff_mapsIntoSimple cs hw).mp hfull
  have hle := card_le_of_mapsIntoSimple cs hm
  have hlt : I.card < (Finset.univ : Finset B).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ I, hI⟩)
  have hc : I.card = (Finset.univ.erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b)] at hle ⊢
    omega
  have he : Finset.univ.erase b =
      @Finset.erase B (Classical.decEq B) Finset.univ b := by
    ext a
    simp
  rw [he] at hc hw hm ⊢
  exact coatom_simpleSurvivor_classification cs b hc hw hm

end Langlands.Group.RelativeWeylIndexing

namespace Langlands.Aubert.General.RationalPointFamily

open SmoothRep GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

local instance rankOneGeometricTermsPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hInter : StandardLeviIntersectionStatement.{u})
  [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hMin : minimalityLengthCriterion actual)

include hLength hSimple hMin hStandard hG hi hν in
omit [TopologicalSpace k] [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [DecidableEq (SimpleRoot i ν)] in
/-- The target's actual normalization witness gives the literal subset equality. -/
theorem pointAssociatedSubset_eq_of_normalizing_longestLift
    (hAssoc : associatedSubsetLaws actual)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) actual)
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep actual J)
    (hself : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J) :
    associatedSubset actual J = J :=
  associatedSubset_eq_of_longestLift_normalizes (levi i ν) (torusPoints i) actual
    hIdent (associatedLeviConjugation_of_standard i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      hN hZ actual hLength hSimple hMin hAssoc) J n hn hself

include hLength hSimple hStandard in
/-- All self terms except the identity and inverse-longest classes vanish
on arbitrary cuspidal data of a maximal standard Levi. -/
theorem pointRankOneSelfTerm_subsingleton_of_other_class
    (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
    (w : Weyl i) (hw : IsMinimal actual J J w)
    (hw1 : w ≠ 1) (hwlong : w ≠ (longestRep actual J)⁻¹)
    (r : Group.RelativeWeyl.normalizer (torusPoints i)) (hr : QuotientGroup.mk r = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J J r)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J J r)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ) :
    Subsingleton ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J r hs ht).obj σ) := by
  apply pointCuspidalGeometricTermVanishing_of_rootComparisons
    i ν hN hZ actual hLength hSimple hStandard hInter hG hi hν hM hU
    J J w hw r hr hs ht σ hc
  intro hfull
  obtain ⟨b, hb⟩ := hJ
  have hJproper : J ≠ Finset.univ := by
    rw [hb]
    exact Finset.erase_ne_self.mpr (Finset.mem_univ b)
  rcases coatom_fullIntersection_classification_of_proper actual b hJproper
      (by simpa only [← hb] using hw) (by simpa only [← hb] using hfull)
      with ⟨_, h1⟩ | ⟨_, hlong⟩
  · exact hw1 h1
  · exact hwlong (by simpa only [← hb] using hlong)

include hLength hSimple hStandard in
/-- Every term toward a different proper standard subset vanishes when the
maximal source subset equals its associate. -/
theorem pointRankOneOtherProperTerm_subsingleton
    (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
    (hself : associatedSubset actual J = J)
    (K : Finset (SimpleRoot i ν)) (hK : K ≠ Finset.univ) (hKJ : K ≠ J)
    (w : Weyl i) (hw : IsMinimal actual K J w)
    (r : Group.RelativeWeyl.normalizer (torusPoints i)) (hr : QuotientGroup.mk r = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) K J r)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) K J r)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ) :
    Subsingleton ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU K J r hs ht).obj σ) := by
  apply pointCuspidalGeometricTermVanishing_of_rootComparisons
    i ν hN hZ actual hLength hSimple hStandard hInter hG hi hν hM hU
    K J w hw r hr hs ht σ hc
  intro hfull
  obtain ⟨b, hb⟩ := hJ
  rcases coatom_fullIntersection_classification_of_proper actual b hK
      (by simpa only [← hb] using hw) (by simpa only [← hb] using hfull)
      with ⟨h, _⟩ | ⟨h, _⟩
  · exact hKJ (h.trans hb.symm)
  · exact hKJ (h.trans (by simpa only [← hb] using hself))

/-- Any lift of the inverse-longest class gives the required inverse
conjugate, for the exact normalizing lift supplied by the rank-one target. -/
def pointRankOneInverseLongestTermIso
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep actual J)
    (hself : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J)
    (r : Group.RelativeWeyl.normalizer (torusPoints i))
    (hr : QuotientGroup.mk r = (longestRep actual J)⁻¹)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J J r)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J J r)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J r hs ht).obj σ ≅
      (conjugationFunctor (n : RationalPoint k G.X)⁻¹
        (fun x => by simpa using hself x)).obj σ := by
  apply geometricTermSameWeylClassIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    (torusPoints i) J J (hZ ▸ centralizerPoints_le_levi i ν J) r n⁻¹
    (by rw [QuotientGroup.mk_inv, hn]; exact hr) hs ht

end Langlands.Aubert.General.RationalPointFamily
