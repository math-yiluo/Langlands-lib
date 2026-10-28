import Langlands.Representation.Classification.SegmentProductAdjacentReplacement
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence

/-! Actual segment-product data inside an ordered block refinement. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.SegmentProductDatum

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ}

/-- The complete ordered list includes every supplied actual representation. -/
theorem blockList_injective :
    Function.Injective (blockList : SegmentProductDatum.{uV,uF} T n →
      List (SegmentBlock.{uF,uV} T)) := by
  rintro ⟨l, Δ, h, A⟩ ⟨l', Δ', h', A'⟩ he
  have hl : l = l' := by
    simpa only [blockList, List.length_ofFn] using congrArg List.length he
  subst l'
  have hi := congrFun (List.ofFn_injective he)
  have hΔ : Δ = Δ' := funext fun i => congrArg Sigma.fst (hi i)
  subst Δ'
  have hA : A = A' := funext fun i => eq_of_heq (Sigma.mk.inj_iff.mp (hi i)).2
  subst A'
  rfl

/-- Rebuilding the complete list of supplied actual blocks recovers the datum. -/
@[simp]
theorem ofBlockList_blockList (d : SegmentProductDatum.{uV,uF} T n) :
    ofBlockList d.blockList d.blockList_degree_sum = d :=
  blockList_injective (blockList_ofBlockList _ _)

/-- Equality of the actual occurrence lists gives an actual product equivalence. -/
def inducedEquivOfBlockListEq (d d' : SegmentProductDatum.{uV,uF} T n)
    (h : d.blockList = d'.blockList) :
    letI := T.topology
    d.induced.representation.Equiv d'.induced.representation := by
  letI := T.topology
  have hd := blockList_injective h
  subst d'
  exact Representation.Equiv.refl _

/-- Express a datum's product using any equal ordered shape and the exact rank
transports of its original factors. -/
def inducedEquivOfShape (d : SegmentProductDatum.{uV,uF} T n)
    (B : BlockShape n) (hl : B.length = d.length)
    (hs : ∀ i, B.size i = (d.segments (Fin.cast hl i)).degree) :
    letI := T.topology
    d.induced.representation.Equiv
      (((T.normalizedProductInductionFunctor B).obj
        (fun i => (hs i).symm ▸ d.blocks (Fin.cast hl i))).representation) := by
  letI := T.topology
  have hB : B = d.shape := BlockShape.ext_of_size hl hs
  subst B
  exact Representation.Equiv.refl _

variable (d : SegmentProductDatum.{uV,uF} T n)
  (D : BlockShape n) (S : BlockRefinement D)
  (e : ((k : Fin D.length) × Fin (S k).length) ≃ Fin d.length)
  (hs : ∀ a, (S a.1).size a.2 = (d.segments (e a)).degree)

/-- Actual original segment occurrences in one component of a refinement. -/
def refinementDatum (k : Fin D.length) : SegmentProductDatum.{uV,uF} T (D.size k) where
  length := (S k).length
  segments l := d.segments (e ⟨k,l⟩)
  degree_sum := by
    calc
      ∑ l, (d.segments (e ⟨k,l⟩)).degree = ∑ l, (S k).size l :=
        Finset.sum_congr rfl fun l _ => (hs ⟨k,l⟩).symm
      _ = D.size k := (S k).sum_eq
  blocks l := d.blocks (e ⟨k,l⟩)

@[simp]
theorem refinementDatum_blockList (k : Fin D.length) :
    (d.refinementDatum D S e hs k).blockList =
      List.ofFn (fun l => d.blockAt (e ⟨k,l⟩)) := rfl

/-- The supplied geometric refinement is exactly the shape of its actual datum. -/
theorem refinementDatum_shape (k : Fin D.length) :
    (d.refinementDatum D S e hs k).shape = S k :=
  BlockShape.ext_of_size rfl fun l => (hs ⟨k,l⟩).symm

/-- Identify each geometric inner product with its actual segment-product datum. -/
def refinementDatumProductEquiv (k : Fin D.length) :
    letI := T.topology
    (((T.normalizedProductInductionFunctor (S k)).obj
      (fun l => (hs ⟨k,l⟩).symm ▸ d.blocks (e ⟨k,l⟩))).representation).Equiv
      (d.refinementDatum D S e hs k).induced.representation := by
  letI := T.topology
  exact (inducedEquivOfShape (d.refinementDatum D S e hs k) (S k) rfl
    (fun l => hs ⟨k,l⟩)).symm

/-- Closed ordered regrouping with actual inner segment-product data. -/
def refinementInducedEquiv
    (hc : ∀ k l (x : Fin ((S k).size l)),
      D.index k ((S k).index l x) =
        d.shape.index (e ⟨k,l⟩) (Fin.cast (hs ⟨k,l⟩) x)) :
    letI := T.topology
    d.induced.representation.Equiv
      (T.normalizedProductInduced D
        (fun k => (d.refinementDatum D S e hs k).induced.representation)) := by
  letI := T.topology
  exact T.normalizedProductRegroupingToEquiv (Parabolic.orderedProductRegrouping F T)
    d.shape D S e hs hc d.blocks
    (fun k => (d.refinementDatum D S e hs k).induced.representation)
    (d.refinementDatumProductEquiv D S e hs)

end Langlands.PadicField.TopologicalData.SegmentProductDatum
