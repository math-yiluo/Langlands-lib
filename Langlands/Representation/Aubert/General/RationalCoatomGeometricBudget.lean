import Langlands.Representation.Aubert.General.RationalGeometricFiltrationCollapse
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Group.RelativeWeylCoatomSurvivors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Actual coatom Jacquet lengths from geometric filtrations -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v uB uW

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Counting

open Group.RelativeWeylIndexing

variable {B : Type uB} {W : Type uW} [Group W] [Fintype B] [Fintype W] [DecidableEq B]
  {C : CoxeterMatrix B} (cs : CoxeterSystem C W)

/-- The original grade occurrences with full source intersection, retaining
both their literal target-coatom label and their index within its grade family. -/
def coatomFullSourceIndices (b : B) (m : B → ℕ) (w : ∀ a, Fin (m a) → W) :
    Finset (Σ a : B, Fin (m a)) :=
  Finset.univ.sigma fun a => Finset.univ.filter fun q =>
    intersectionSubset cs (Finset.univ.erase a) (Finset.univ.erase b) (w a q) =
      Finset.univ.erase b

/-- Count every occurrence of a full-source minimal class over all literal
coatom labels. Injectivity is required within each original grade family. -/
theorem coatomFullSourceIndicatorBudget (b : B) (m : B → ℕ)
    (w : ∀ a, Fin (m a) → W)
    (hmin : ∀ a q, IsMinimal cs (Finset.univ.erase a) (Finset.univ.erase b) (w a q))
    (hinj : ∀ a, Function.Injective (w a)) :
    (∑ a, ∑ q, if intersectionSubset cs (Finset.univ.erase a)
      (Finset.univ.erase b) (w a q) = Finset.univ.erase b then (1 : ℕ∞) else 0) ≤ 2 := by
  let S := coatomFullSourceIndices cs b m w
  let f : (Σ a : B, Fin (m a)) → Finset B × W :=
    fun x => (Finset.univ.erase x.1, w x.1 x.2)
  have hmap : Set.MapsTo f S (fullIntersectionPairs cs (Finset.univ.erase b)) := by
    rintro ⟨a, q⟩ hq
    have hfull := (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
    change (Finset.univ.erase a, w a q) ∈ fullIntersectionPairs cs (Finset.univ.erase b)
    simp only [fullIntersectionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hmin a q, hfull⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_erase_of_mem (Finset.mem_univ b)]
  have hf : (S : Set (Σ a : B, Fin (m a))).InjOn f := by
    rintro ⟨a, q⟩ _ ⟨a', q'⟩ _ he
    have haa : a = a' := (Finset.erase_inj _ (Finset.mem_univ a)).mp
      (congrArg Prod.fst he)
    subst a'
    have hqq : q = q' := hinj a (congrArg Prod.snd he)
    subst q'
    rfl
  have hcanonical : @Finset.erase B ‹DecidableEq B› Finset.univ b =
      @Finset.erase B (Classical.decEq B) Finset.univ b := by
    ext a
    simp
  have hcoatom : (fullIntersectionPairs cs (Finset.univ.erase b)).card ≤ 2 := by
    rw [hcanonical]
    exact card_fullIntersectionPairs_coatom_le_two cs b
  have hcount : S.card ≤ 2 :=
    (Finset.card_le_card_of_injOn f hmap hf).trans hcoatom
  calc
    _ = (S.card : ℕ∞) := by simp [S, coatomFullSourceIndices, Finset.card_sigma, Nat.cast_sum]
    _ ≤ 2 := by exact_mod_cast hcount

end Counting

namespace RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)

local instance rationalCoatomGeometricBudgetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

include hLength hSimple hG hi hν hStandard in
omit [DecidableEq (SimpleRoot i ν)] in
/-- A full source intersection between equally large standard subsets makes
an actual geometric term irreducible when its original source is irreducible. -/
theorem pointGeometricTerm_isIrreducible_of_full_source_of_card
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (hfull : intersectionSubset cs I J w = J) (hcard : J.card = I.card)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.IsIrreducible) :
    ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht).obj σ).IsIrreducible := by
  have hA : rootAssociation i ν hN hZ J I (n : RationalPoint k G.X) := by
    refine ⟨n.property, ?_⟩
    change weylCharacterAction i hN hZ (QuotientGroup.mk n) '' rootSet i ν J = _
    rw [hn]
    exact rootImage_eq_of_full_intersection i ν hN hZ cs hLength hSimple
      (minimalityLengthCriterion_proof cs) hw hfull hcard
  exact smooth_isIrreducible_of_iso_pullback
    (rootAssociationLeviConjugationEquiv i ν hG hi hν hStandard hN hZ J I n hA)
    σ _ (pointGeometricTermRootAssociationIso
      i ν hG hi hν hStandard hN hZ hM hU I J n hA hs ht σ) hσ

include hLength hSimple hG hi hν hStandard in
/-- On cuspidal irreducible input, an equal-rank actual geometric term has
length one precisely at a full source intersection and length zero otherwise. -/
theorem pointGeometricTerm_repLength
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J n)
    (hcard : J.card = I.card)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.IsIrreducible)
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ) :
    repLength ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J n hs ht).obj σ).representation =
      if intersectionSubset cs I J w = J then 1 else 0 := by
  by_cases hfull : intersectionSubset cs I J w = J
  · rw [ite_eq_left hfull]
    exact repLength_eq_one_iff.mpr
      (pointGeometricTerm_isIrreducible_of_full_source_of_card.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hStandard hM hU
        I J w hw n hn hs ht hfull hcard σ hσ)
  · rw [ite_eq_right hfull]
    exact repLength_eq_zero_iff.mpr
      (pointCuspidalGeometricTermVanishing_of_rootComparisons.{u, v}
        i ν hN hZ cs hLength hSimple hStandard hInter hG hi hν hM hU
        I J w hw n hn hs ht σ hc hfull)


variable [Fintype (Weyl i)]

include hLength hSimple hG hi hν hStandard in
/-- Actual finite filtrations with distinct minimal Weyl classes give the
entire coatom Jacquet-length budget, including both association cases. -/
theorem pointCoatomJacquetBudget_of_geometricFiltrations
    (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
    (hσ : σ.IsIrreducible)
    (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ)
    (m : SimpleRoot i ν → ℕ) (w : ∀ a, Fin (m a) → Weyl i)
    (hmin : ∀ a q, IsMinimal cs (Finset.univ.erase a) J (w a q))
    (hinj : ∀ a, Function.Injective (w a))
    (n : ∀ a, Fin (m a) → Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : ∀ a q, QuotientGroup.mk (n a q) = w a q)
    (hs : ∀ a q, GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) (Finset.univ.erase a) J (n a q))
    (ht : ∀ a q, GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) (Finset.univ.erase a) J (n a q))
    (s : ∀ a, ObjectRepFiltration
      (pointInducedJacquetObject i ν hG hi hν hStandard hU (Finset.univ.erase a) J σ).obj
      (m a))
    (grades : ∀ a q, (s a).gradedRepresentation q ≅
      ((geometricTermFunctor.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
        (Finset.univ.erase a) J (n a q) (hs a q) (ht a q)).obj σ).obj) :
    (∑ a, repLength (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (Finset.univ.erase a) J σ).representation) ≤ 2 := by
  obtain ⟨b, rfl⟩ := hJ
  calc
    _ = ∑ a, ∑ q, if intersectionSubset cs (Finset.univ.erase a)
        (Finset.univ.erase b) (w a q) = Finset.univ.erase b then (1 : ℕ∞) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [repLength_eq_sum_of_filtration (s a)]
      apply Finset.sum_congr rfl
      intro q _
      rw [repLength_congr (Representation.equivOfIso (grades a q))]
      apply pointGeometricTerm_repLength.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
        (Finset.univ.erase a) (Finset.univ.erase b) (w a q) (hmin a q)
        (n a q) (hn a q) (hs a q) (ht a q) _ σ hσ hc
      rw [Finset.card_erase_of_mem (Finset.mem_univ b),
        Finset.card_erase_of_mem (Finset.mem_univ a)]
    _ ≤ 2 := coatomFullSourceIndicatorBudget cs b m w hmin hinj

end RationalPointFamily

end Langlands.Aubert.General
