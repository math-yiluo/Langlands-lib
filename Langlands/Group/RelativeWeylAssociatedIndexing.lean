import Langlands.Group.RelativeWeylJacquetProof
import Langlands.Group.RelativeWeylAssociatedSubsetProof
import Mathlib.Data.Finset.Image

/-! # Simple-label and subset transport for the longest representative -/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
open scoped BigOperators
noncomputable section

private theorem mem_simpleImage_iff [Fintype B] (w : W) (I : Finset B) (j : B) :
    j ∈ simpleImage cs w I ↔ ∃ i ∈ I, w * cs.simple i * w⁻¹ = cs.simple j := by
  simp [simpleImage]

/-- Conjugation gives an equivalence of the actual simple-label subtypes when
every source label has a simple image and those images cover the target. -/
def simpleConjugationEquiv [Fintype B] (w : W) (I J : Finset B)
    (hm : MapsIntoSimple cs w I J) (hc : simpleImage cs w I = J) : I ≃ J :=
  Equiv.ofBijective
    (fun i => ⟨Classical.choose (hm i i.property), (Classical.choose_spec
      (hm i i.property)).1⟩)
    ⟨by
      intro i k he
      apply Subtype.ext
      apply simple_reflection_injective cs
      apply mul_left_cancel (a := w)
      apply mul_right_cancel (b := w⁻¹)
      exact (Classical.choose_spec (hm i i.property)).2.trans
        ((congrArg cs.simple (Subtype.ext_iff.mp he)).trans
          (Classical.choose_spec (hm k k.property)).2.symm),
    by
      intro j
      obtain ⟨i, hi, hij⟩ :=
        (mem_simpleImage_iff cs w I j).mp (hc.symm ▸ j.property)
      refine ⟨⟨i, hi⟩, Subtype.ext (simple_reflection_injective cs ?_)⟩
      exact (Classical.choose_spec (hm i hi)).2.symm.trans hij⟩

theorem simpleConjugationEquiv_conj [Fintype B] (w : W) (I J : Finset B)
    (hm : MapsIntoSimple cs w I J) (hc : simpleImage cs w I = J) (i : I) :
    w * cs.simple i * w⁻¹ =
      cs.simple (simpleConjugationEquiv cs w I J hm hc i) :=
  (Classical.choose_spec (hm i i.property)).2

/-- The associated labels are carried to `J` by the specified longest
representative, using the inverse simple-label bijection in the definition
of `associatedSubset`. -/
def associatedSimpleEquiv [Fintype B] [Fintype W] (J : Finset B) :
    associatedSubset cs J ≃ J :=
  (simpleConjugationEquiv cs (longestRep cs J)⁻¹ J (associatedSubset cs J)
    (by
      intro j hj
      obtain ⟨i, _, hi⟩ := (associatedSubsetLaws_proof cs J).1 j hj
      exact ⟨i, (mem_simpleImage_iff cs _ _ _).mpr ⟨j, hj, hi⟩, hi⟩)
    rfl).symm

theorem associatedSimpleEquiv_conj [Fintype B] [Fintype W] (J : Finset B)
    (i : associatedSubset cs J) :
    longestRep cs J * cs.simple i * (longestRep cs J)⁻¹ =
      cs.simple (associatedSimpleEquiv cs J i) := by
  have h := simpleConjugationEquiv_conj cs (longestRep cs J)⁻¹ J
    (associatedSubset cs J)
    (by
      intro j hj
      obtain ⟨i, _, hi⟩ := (associatedSubsetLaws_proof cs J).1 j hj
      exact ⟨i, (mem_simpleImage_iff cs _ _ _).mpr ⟨j, hj, hi⟩, hi⟩)
    rfl (associatedSimpleEquiv cs J i)
  change (longestRep cs J)⁻¹ *
      cs.simple (associatedSimpleEquiv cs J i) * ((longestRep cs J)⁻¹)⁻¹ =
      cs.simple ((associatedSimpleEquiv cs J).symm
        (associatedSimpleEquiv cs J i)) at h
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  group

/-- The induced equivalence between the actual finite-subset index types of
the associated Levi and the target Levi. -/
def associatedFinsetEquiv [Fintype B] [Fintype W] (J : Finset B) :
    Finset (associatedSubset cs J) ≃ Finset J :=
  (associatedSimpleEquiv cs J).finsetCongr

@[simp]
theorem card_associatedFinsetEquiv [Fintype B] [Fintype W] (J : Finset B)
    (I : Finset (associatedSubset cs J)) :
    (associatedFinsetEquiv cs J I).card = I.card :=
  Finset.card_map _

/-- The finite-subset equivalence is literally the simple-reflection image
after both subtype index sets are read in the ambient label type. -/
theorem simpleImage_associatedFinsetEquiv [Fintype B] [Fintype W]
    (J : Finset B) (I : Finset (associatedSubset cs J)) :
    simpleImage cs (longestRep cs J)
        (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))) =
      (associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J)) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, hij⟩ := (mem_simpleImage_iff cs _ _ _).mp hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    have he : (associatedSimpleEquiv cs J a : B) = j :=
      simple_reflection_injective cs ((associatedSimpleEquiv_conj cs J a).symm.trans hij)
    exact Finset.mem_map.mpr ⟨associatedSimpleEquiv cs J a,
      Finset.mem_map.mpr ⟨a, ha, rfl⟩, he⟩
  · intro hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact (mem_simpleImage_iff cs _ _ _).mpr
      ⟨a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, associatedSimpleEquiv_conj cs J a⟩

omit cs in
/-- Reindex a sum over the subsets of `J` by the literal finite subsets of
the subtype `J`. This is the index convention of the Levi operator. -/
theorem sum_powerset_eq_sum_finset_subtype {A : Type*} [AddCommMonoid A]
    (J : Finset B) (f : Finset B → A) :
    (∑ K ∈ J.powerset, f K) =
      ∑ I : Finset J, f (I.map (Function.Embedding.subtype (· ∈ J))) := by
  symm
  apply Finset.sum_bij
    (fun I _ => I.map (Function.Embedding.subtype (· ∈ J)))
  · intro I _
    exact Finset.mem_powerset.mpr (fun _ h =>
      Finset.property_of_mem_map_subtype I h)
  · intro I _ K _ h
    exact Finset.map_injective _ h
  · intro K hK
    refine ⟨K.subtype (· ∈ J), Finset.mem_univ _, ?_⟩
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp hK)
  · intro I _
    rfl

/-- Reindex the unadjusted signed survivor sum by the actual finite-subset
labels of the associated Levi. -/
theorem signed_sum_associatedFinsetEquiv [Fintype B] [Fintype W]
    {A : Type*} [AddCommGroup A] (J : Finset B) (f : Finset B → A) :
    (∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • f K) =
      ∑ I : Finset (associatedSubset cs J), ((-1 : ℤ) ^ I.card) •
        f (simpleImage cs (longestRep cs J)
          (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J)))) := by
  rw [sum_powerset_eq_sum_finset_subtype]
  symm
  apply Fintype.sum_equiv (associatedFinsetEquiv cs J)
  intro I
  rw [simpleImage_associatedFinsetEquiv, Finset.card_map,
    card_associatedFinsetEquiv]

/-- The right ascents of the longest representative are exactly the
associated simple labels; no sign choice or root relabeling is needed. -/
theorem positiveSimpleSet_longestRep [Fintype B] [Fintype W] (J : Finset B) :
    positiveSimpleSet cs (longestRep cs J) = associatedSubset cs J := by
  set w := longestRep cs J
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := mapsIntoSimple_longestRep cs J i hi
    change w * cs.simple i * w⁻¹ = cs.simple j at hij
    apply (mem_simpleImage_iff cs w⁻¹ J i).mpr
    refine ⟨j, hj, ?_⟩
    rw [← hij]
    group
  · intro hi
    obtain ⟨j, hj, hji⟩ := (mem_simpleImage_iff cs w⁻¹ J i).mp hi
    have hconj : w * cs.simple i = cs.simple j * w := by
      rw [← hji]
      group
    apply (mem_positiveSimpleSet cs w i).mpr
    rw [hconj]
    exact ((minimalityLengthCriterion_proof cs J ∅ w).mp
      ((mem_minimalReps cs J ∅ w).mp (longestRep_mem cs J))).1 j hj

end
end Langlands.Group.RelativeWeylIndexing
