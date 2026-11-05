import Langlands.Representation.Classification.SegmentHeadProductFiniteness
import Langlands.Representation.Classification.SegmentProductAdjacentRefinement
import Langlands.Representation.Parabolic.WholeLeviConjugacyProof
import Langlands.Representation.Parabolic.ProductInductionSubrepresentation
import Langlands.Representation.Filtration.IrreducibleExactComparison
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction

/-! Actual extraction of two supplied head occurrences from an irreducible product. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Choose an actual nonzero vector in any product of supplied special heads. -/
def segmentHeadProductNonzeroVector {n : ℕ} (d : T.SegmentProductDatum.{uV,uF} n)
    (hd : d.HasSegmentHeads) :
    letI := T.topology
    {v : d.induced // v ≠ 0} := by
  classical
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI : ∀ i, Representation.IsIrreducible (d.blocks i).representation :=
    fun i => (hd i).isIrreducible
  letI : ∀ i, Nontrivial (d.blocks i) := fun i =>
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (d.segments i).degree F.Carrier))
      (d.blocks i).representation.asModule
  let b := fun i => Module.Basis.ofVectorSpace ℂ (d.blocks i)
  let bt := Basis.piTensorProduct b
  let q := fun i => Classical.choice (b i).index_nonempty
  have hσ : IsSmooth (d.shape.blockTensor (fun i => (d.blocks i).representation)) :=
    FiniteTensor.isSmooth_external _ (fun i => (d.blocks i).isSmooth)
  refine Classical.choice ?_
  obtain ⟨f, hf⟩ := CuspidalSupport.normalizedParabolicInduced_eval_surjective
    T d.shape (d.shape.blockTensor (fun i => (d.blocks i).representation)) hσ (bt q)
  refine ⟨⟨f, ?_⟩⟩
  intro hz
  apply bt.ne_zero q
  rw [← hf, hz]
  rfl

/-- Under whole-product irreducibility an arbitrary permutation is realized by
an actual representation equivalence, not just by equality of constituents. -/
def segmentHeadProductPermutationEquiv {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (hirr : letI := T.topology; d.induced.IsIrreducible)
    (σ : Equiv.Perm (Fin d.length)) :
    letI := T.topology
    d.induced.representation.Equiv (d.permute σ).induced.representation := by
  letI := T.topology
  exact Classical.choice (RepresentationExactComparison.nonempty_equiv_of_sameFactors
    (Rep.of d.induced.representation) (Rep.of (d.permute σ).induced.representation) hirr
    (Parabolic.WholeLeviConjugacyProof.permutedProducts F T hn d.shape σ d.blocks
      (fun i => (hd i).isIrreducible) (fun i => (hd i).isAdmissible)))

/-- Every actual inner datum of the adjacent merge inherits its head proofs. -/
theorem segmentAdjacentDatum_hasSegmentHeads {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (j : ℕ) (h : j + 1 < d.length)
    (k : Fin (d.shape.adjacentMerge j h).length) :
    (d.adjacentDatum j h k).HasSegmentHeads :=
  fun l => hd (d.shape.adjacentBlockEquiv j h ⟨k,l⟩)

/-- Irreducibility of the whole product forces irreducibility of the actual
adjacent pair after regrouping. -/
theorem segmentAdjacentDatum_isIrreducible {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (hirr : let := T.topology; d.induced.IsIrreducible)
    (j : ℕ) (h : j + 1 < d.length) :
    let := T.topology
    (d.adjacentDatum j h (d.shape.adjacentMergeIndex j h)).induced.IsIrreducible := by
  classical
  let := T.topology
  let B := d.shape.adjacentMerge j h
  let A := fun k => (d.adjacentDatum j h k).induced
  let a := d.shape.adjacentMergeIndex j h
  let : ∀ k, Nontrivial (A k) := fun k =>
    ⟨⟨(segmentHeadProductNonzeroVector T _
      (segmentAdjacentDatum_hasSegmentHeads T d hd j h k)).val, 0,
      (segmentHeadProductNonzeroVector T _
      (segmentAdjacentDatum_hasSegmentHeads T d hd j h k)).property⟩⟩
  have ho : Representation.IsIrreducible
      (T.normalizedProductInduced B (fun k => (A k).representation)) :=
    LengthTwo.isIrreducible_of_equiv (d.adjacentInducedEquiv j h) hirr
  let := ho
  let ρ := fun k => (A k).representation
  let : Nontrivial (Subrepresentation (ρ a)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    obtain ⟨v, hv⟩ := exists_ne (0 : A a)
    apply hv
    have hv' : v ∈ (⊥ : Subrepresentation (ρ a)) := by
      rw [he]
      trivial
    exact hv'
  change IsSimpleOrder (Subrepresentation (ρ a))
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  by_contra htop
  obtain ⟨h₀,h₁⟩ := Parabolic.normalizedProductSlotSubrepresentation_proper_nonzero
    T B ρ a (fun k => inferInstance) S hS htop (fun k => (A k).isSmooth)
  rcases eq_bot_or_eq_top (Parabolic.normalizedProductSlotSubrepresentation T B ρ a S)
    with he | he
  · exact h₀ he
  · exact h₁ he

/-- Place two distinct finite labels at the first two positions. -/
private def pairFrontPermutation {L : ℕ} (hL : 1 < L)
    (i j : Fin L) (hij : i ≠ j) :
    {σ : Equiv.Perm (Fin L) //
      σ ⟨0, by omega⟩ = i ∧ σ ⟨1, hL⟩ = j} := by
  classical
  let a : Fin L := ⟨0, by omega⟩
  let b : Fin L := ⟨1, hL⟩
  let e := Equiv.swap a i
  let k := e.symm j
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hka : k ≠ a := by
    intro h
    have he := congrArg e h
    have hji : j = i := by
      simpa only [k, Equiv.apply_symm_apply, e, Equiv.swap_apply_left] using he
    exact hij hji.symm
  refine ⟨(Equiv.swap b k).trans e, ?_, ?_⟩
  · change e (Equiv.swap b k a) = i
    rw [Equiv.swap_apply_of_ne_of_ne hab hka.symm]
    exact Equiv.swap_apply_left _ _
  · change e (Equiv.swap b k b) = j
    rw [Equiv.swap_apply_left]
    exact e.apply_symm_apply j

/-- Actual extraction data for two selected supplied head occurrences. -/
structure SegmentHeadProductPairReduction {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (i j : Fin d.length) where
  length_gt_one : 1 < d.length
  permutation : Equiv.Perm (Fin d.length)
  first_eq : permutation ⟨0, by omega⟩ = i
  second_eq : permutation ⟨1, length_gt_one⟩ = j
  permutationEquiv : letI := T.topology
    d.induced.representation.Equiv (d.permute permutation).induced.representation
  datum : T.SegmentProductDatum.{uV,uF}
    ((d.segments i).degree + (d.segments j).degree)
  heads : datum.HasSegmentHeads
  blocks_eq : datum.blockList = [d.blockAt i, d.blockAt j]
  irreducible : letI := T.topology
    datum.induced.IsIrreducible

/-- Transport a complete pair package only along equality of its natural rank. -/
private def transportHeadPair {m k : ℕ} (h : m = k)
    (l : List (SegmentBlock.{uF,uV} T)) (a : T.SegmentProductDatum.{uV,uF} m)
    (ha : a.HasSegmentHeads) (hb : a.blockList = l)
    (hi : letI := T.topology; a.induced.IsIrreducible) :
    {b : T.SegmentProductDatum.{uV,uF} k // b.HasSegmentHeads ∧ b.blockList = l ∧
      (letI := T.topology; b.induced.IsIrreducible)} := by
  subst k
  exact ⟨a, ha, hb, hi⟩

/-- Extract any two distinct occurrences from an irreducible special-head
product as actual irreducible two-block data, preserving the supplied blocks. -/
def segmentHeadProductPairReduction {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (hirr : letI := T.topology; d.induced.IsIrreducible)
    (i j : Fin d.length) (hij : i ≠ j) :
    SegmentHeadProductPairReduction T d i j := by
  classical
  letI := T.topology
  have hl : 1 < d.length := by
    have hi := i.isLt
    have hj := j.isLt
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  rcases pairFrontPermutation hl i j hij with ⟨σ, h0, h1⟩
  let e := segmentHeadProductPermutationEquiv T hn d hd hirr σ
  let D := d.permute σ
  have hD : D.HasSegmentHeads := hd.permute σ
  have hDi : D.induced.IsIrreducible := LengthTwo.isIrreducible_of_equiv e hirr
  let E := D.adjacentDatum 0 hl (D.shape.adjacentMergeIndex 0 hl)
  have hE : E.HasSegmentHeads :=
    segmentAdjacentDatum_hasSegmentHeads T D hD 0 hl _
  have hEi : E.induced.IsIrreducible :=
    segmentAdjacentDatum_isIrreducible T D hD hDi 0 hl
  have hEb : E.blockList = [d.blockAt i, d.blockAt j] := by
    rw [D.adjacentDatum_merged_blockList 0 hl]
    change [d.blockAt (σ ⟨0, by omega⟩), d.blockAt (σ ⟨1, hl⟩)] = _
    rw [h0, h1]
  have hr : (D.shape.adjacentMerge 0 hl).size (D.shape.adjacentMergeIndex 0 hl) =
      (d.segments i).degree + (d.segments j).degree := by
    have hs := E.blockList_degree_sum
    rw [hEb] at hs
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, SegmentProductDatum.blockAt] using hs.symm
  rcases transportHeadPair T hr [d.blockAt i, d.blockAt j] E hE hEb hEi with
    ⟨a, ha, hb, hi⟩
  exact { length_gt_one := hl
          permutation := σ
          first_eq := h0
          second_eq := h1
          permutationEquiv := e
          datum := a
          heads := ha
          blocks_eq := hb
          irreducible := hi }

end Langlands.Classification
