import Langlands.Representation.Classification.LinkedSegmentSocleEmbeddingReductionStatement
import Langlands.Representation.Classification.LinkedSegmentSocleGluingProof
import Langlands.Representation.Classification.SegmentProductSlotReplacement
import Langlands.Representation.Parabolic.RegroupedProductFiltration
import Langlands.Representation.Filtration.IrreducibleEmbedding

/-!
# Proof of the local linked-segment socle embedding reduction

Zelevinsky 1980, §6.7: merge the adjacent linked pair `Δ', Δ` of a segment-socle
product into one slot of a regrouped product, filter that slot by the length-two
gluing filtration of the forward pair product, and send an irreducible
subrepresentation of the full product into one of the two resulting outer
products: the product with the pair swapped, or the product with the pair
replaced by its union and intersection.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear Geometric PadicField.TopologicalData

universe uF uV uW uX uY

section TwoLayers

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((k : Fin D.length) × Fin (S k).length) ≃ Fin B.length)
  (h : ∀ a, (S a.1).size a.2 = B.size (e a))
  (hc : ∀ k l (x : Fin ((S k).size l)),
    D.index k ((S k).index l x) = B.index (e ⟨k,l⟩) (Fin.cast (h ⟨k,l⟩) x))
  (σ : letI := T.topology
    ∀ k, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size k) F.Carrier))
  {W : Fin D.length → Type uW}
  [∀ k, AddCommGroup (W k)] [∀ k, Module ℂ (W k)]
  (τ : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (W k))
  (δ : letI := T.topology
    ∀ k, Representation.Equiv
      (((T.normalizedProductInductionFunctor.{uF,uV} (S k)).obj
        (fun l => (h ⟨k,l⟩).symm ▸ σ (e ⟨k,l⟩))).representation) (τ k))
  (j : Fin D.length) (s : ObjectRepFiltration (Rep.of (τ j)) 2)

include hc δ in
/-- An irreducible representation embedded in an ordered product embeds into one
of two outer replacement products of a regrouping, one for each graded piece of
a length-two filtration of a single inner product. -/
theorem exists_injective_regroupedProduct_two_layers (i i' : Fin 2) (hii : i ≠ i')
    {X X' : Fin D.length → Type uX}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, AddCommGroup (X' k)] [∀ k, Module ℂ (X' k)]
    (υ : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (X k))
    (υ' : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (X' k))
    (a : ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (υ k))
    (b : (s.gradedRepresentation i).ρ.IntertwiningMap (υ j)) (hb : Function.Injective b)
    (a' : ∀ k : ({j}ᶜ : Set (Fin D.length)), (τ k).Equiv (υ' k))
    (b' : (s.gradedRepresentation i').ρ.IntertwiningMap (υ' j))
    (hb' : Function.Injective b')
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    (π : Representation ℂ (GeneralLinear n F.Carrier) Y) :
    letI := T.topology
    (∀ k, IsSmooth (τ k)) → π.IsIrreducible →
      ∀ f : π.IntertwiningMap
        (((T.normalizedProductInductionFunctor B).obj σ).representation),
        Function.Injective f →
          (∃ g : π.IntertwiningMap (T.normalizedProductInduced D υ), Function.Injective g) ∨
            ∃ g : π.IntertwiningMap (T.normalizedProductInduced D υ'),
              Function.Injective g := by
  let := T.topology
  intro hτ hπ f hf
  have hex := (Parabolic.regroupedProductSlotFiltration T B D S e h hc σ τ δ j s).exists_injective_graded
    f hπ hf
  obtain ⟨k, g, hg⟩ := hex
  have hk : k = i ∨ k = i' := by omega
  rcases hk with rfl | rfl
  · exact Or.inl ⟨(Parabolic.regroupedProductSlotFiltrationGradedMap T B D S e h hc σ τ δ j s
        υ k a b hτ).comp g,
      (Parabolic.regroupedProductSlotFiltrationGradedMap_injective T B D S e h hc σ τ δ j s
        υ k a b hb hτ).comp hg⟩
  · exact Or.inr ⟨(Parabolic.regroupedProductSlotFiltrationGradedMap T B D S e h hc σ τ δ j s
        υ' k a' b' hτ).comp g,
      (Parabolic.regroupedProductSlotFiltrationGradedMap_injective T B D S e h hc σ τ δ j s
        υ' k a' b' hb' hτ).comp hg⟩

end TwoLayers

section RefinementTwoLayers

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (d : T.SegmentProductDatum.{uV, uF} n) (D : BlockShape n) (S : BlockRefinement D)
  (e : ((k : Fin D.length) × Fin (S k).length) ≃ Fin d.length)
  (hs : ∀ a, (S a.1).size a.2 = (d.segments (e a)).degree)
  (hc : ∀ k l (x : Fin ((S k).size l)),
    D.index k ((S k).index l x) = d.shape.index (e ⟨k,l⟩) (Fin.cast (hs ⟨k,l⟩) x))
  (j : Fin D.length)
  (s : letI := T.topology
    ObjectRepFiltration (Rep.of (d.refinementDatum D S e hs j).induced.representation) 2)

include hc in
/-- The two-layer embedding for the actual inner segment-product data of a
refinement of a segment product. -/
theorem exists_injective_of_refinement_slot_two_layers (i i' : Fin 2) (hii : i ≠ i')
    {X X' : Fin D.length → Type uX}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, AddCommGroup (X' k)] [∀ k, Module ℂ (X' k)]
    (υ : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (X k))
    (υ' : ∀ k, Representation ℂ (GeneralLinear (D.size k) F.Carrier) (X' k))
    (a : letI := T.topology
      ∀ k : ({j}ᶜ : Set (Fin D.length)),
        ((d.refinementDatum D S e hs k).induced.representation).Equiv (υ k))
    (b : (s.gradedRepresentation i).ρ.IntertwiningMap (υ j)) (hb : Function.Injective b)
    (a' : letI := T.topology
      ∀ k : ({j}ᶜ : Set (Fin D.length)),
        ((d.refinementDatum D S e hs k).induced.representation).Equiv (υ' k))
    (b' : (s.gradedRepresentation i').ρ.IntertwiningMap (υ' j))
    (hb' : Function.Injective b')
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    (π : Representation ℂ (GeneralLinear n F.Carrier) Y) :
    letI := T.topology
    π.IsIrreducible →
      ∀ f : π.IntertwiningMap d.induced.representation, Function.Injective f →
        (∃ g : π.IntertwiningMap (T.normalizedProductInduced D υ), Function.Injective g) ∨
          ∃ g : π.IntertwiningMap (T.normalizedProductInduced D υ'),
            Function.Injective g := by
  let := T.topology
  intro hπ f hf
  exact exists_injective_regroupedProduct_two_layers T d.shape D S e hs hc d.blocks
    (fun k => (d.refinementDatum D S e hs k).induced.representation)
    (d.refinementDatumProductEquiv D S e hs) j s i i' hii υ υ' a b hb a' b' hb' π
    (fun k => (d.refinementDatum D S e hs k).induced.isSmooth) hπ f hf

end RefinementTwoLayers

namespace LinkedReduction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) (j : ℕ) (h : j + 1 < d.length)

/-- The shape merging the adjacent blocks `j` and `j + 1`. -/
abbrev mergeShape : BlockShape n := d.shape.adjacentMerge j h

/-- Its refinement recovering the original blocks. -/
abbrev mergeRefinement : BlockRefinement (mergeShape d j h) :=
  d.shape.adjacentRefinement j h

/-- The consecutive label bijection of the adjacent refinement. -/
abbrev mergeLabel :
    ((k : Fin (mergeShape d j h).length) × Fin (mergeRefinement d j h k).length) ≃
      Fin d.length :=
  d.shape.adjacentBlockEquiv j h

theorem mergeLabel_size
    (a : (k : Fin (mergeShape d j h).length) × Fin (mergeRefinement d j h k).length) :
    (mergeRefinement d j h a.1).size a.2 = (d.segments (mergeLabel d j h a)).degree :=
  d.shape.adjacentBlock_size j h a

/-- The merged slot. -/
abbrev mergeSlot : Fin (mergeShape d j h).length := d.shape.adjacentMergeIndex j h

/-- The actual inner datum of each merged slot, retaining the original blocks. -/
abbrev fiber (k : Fin (mergeShape d j h).length) :
    T.SegmentProductDatum.{uV, uF} ((mergeShape d j h).size k) :=
  d.refinementDatum (mergeShape d j h) (mergeRefinement d j h) (mergeLabel d j h)
    (mergeLabel_size d j h) k

/-- The actual two-block datum of the adjacent pair. -/
abbrev pairDatum :
    T.SegmentProductDatum.{uV, uF} ((mergeShape d j h).size (mergeSlot d j h)) :=
  fiber d j h (mergeSlot d j h)

theorem pairDatum_length : (pairDatum d j h).length = 2 :=
  d.shape.adjacentRefinement_length_merged j h

theorem pairDatum_segments_zero (hx : 0 < (pairDatum d j h).length) :
    (pairDatum d j h).segments ⟨0, hx⟩ = d.segments ⟨j, Nat.lt_of_succ_lt h⟩ :=
  congrArg d.segments (Fin.ext
    ((d.shape.adjacentBlockEquiv_val j h ⟨mergeSlot d j h, ⟨0, hx⟩⟩).trans
      (by change j + 0 + (if j < j then 1 else 0) = j; simp)))

theorem pairDatum_segments_one (hx : 1 < (pairDatum d j h).length) :
    (pairDatum d j h).segments ⟨1, hx⟩ = d.segments ⟨j + 1, h⟩ :=
  congrArg d.segments (Fin.ext
    ((d.shape.adjacentBlockEquiv_val j h ⟨mergeSlot d j h, ⟨1, hx⟩⟩).trans
      (by change j + 1 + (if j < j then 1 else 0) = j + 1; simp)))

theorem fiber_hasSegmentSocles (hd : d.HasSegmentSocles) (k : Fin (mergeShape d j h).length) :
    (fiber d j h k).HasSegmentSocles := fun _ => hd _

/-- The reverse two-block datum of the adjacent pair. -/
abbrev pairReverse :
    T.SegmentProductDatum.{uV, uF} ((mergeShape d j h).size (mergeSlot d j h)) :=
  (pairDatum d j h).permute ((pairDatum d j h).shape.adjacentSwap 0
    (by change 0 + 1 < (pairDatum d j h).length; rw [pairDatum_length]; omega))

end LinkedReduction

open LinkedReduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The local reduction from the gluing of the forward pair product. -/
theorem linkedSegmentSocleEmbeddingReduction_of_gluing
    (hglue : LinkedSegmentSocleGluing.{uF, uV} F T) :
    LinkedSegmentSocleEmbeddingReduction.{uF, uV} F T := by
  let := T.topology
  intro n d π hd hsub j h Δ' Δ hp
  obtain ⟨hπ, f, hf⟩ := hsub
  have hx0 : 0 < (pairDatum d j h).length := by rw [pairDatum_length]; omega
  have hx1 : 1 < (pairDatum d j h).length := by rw [pairDatum_length]; omega
  have h0 := pairDatum_segments_zero d j h hx0
  have h1 := pairDatum_segments_one d j h hx1
  have hp' : ((pairDatum d j h).segments ⟨0, hx0⟩).Precedes
      ((pairDatum d j h).segments ⟨1, hx1⟩) := by
    rw [h0, h1]; exact hp
  obtain ⟨U, I, e₂, hUI, hlist, he₂, s, i, i', hii, ⟨ε⟩, g, hg⟩ :=
    hglue _ (pairDatum d j h) (pairDatum_length d j h)
      (fiber_hasSegmentSocles d j h hd _) hp'
  rw [h0, h1] at hUI
  have a : ∀ k : ({mergeSlot d j h}ᶜ : Set (Fin (mergeShape d j h).length)),
      ((fiber d j h k).induced.representation).Equiv
        ((d.adjacentReplacementDatum j h e₂ k).induced.representation) := fun k =>
    SegmentProductDatum.inducedEquivOfBlockListEq _ _ (congrArg SegmentProductDatum.blockList
      (d.adjacentReplacementDatum_of_ne j h e₂ k k.2).symm)
  have b : (e₂.induced.representation).Equiv
      ((d.adjacentReplacementDatum j h e₂ (mergeSlot d j h)).induced.representation) :=
    SegmentProductDatum.inducedEquivOfBlockListEq _ _ (congrArg SegmentProductDatum.blockList
      (d.adjacentReplacementDatum_merged j h e₂).symm)
  have q := d.replaceAdjacentSlotInducedEquiv j h e₂
  have a' : ∀ k : ({mergeSlot d j h}ᶜ : Set (Fin (mergeShape d j h).length)),
      ((fiber d j h k).induced.representation).Equiv
        ((d.adjacentSwappedDatum j h k).induced.representation) := fun k =>
    SegmentProductDatum.inducedEquivOfBlockListEq _ _ (congrArg SegmentProductDatum.blockList
      (d.adjacentSwappedDatum_of_ne j h k (fun hk => k.2 (Fin.ext hk))).symm)
  have b' : ((pairReverse d j h).induced.representation).Equiv
      ((d.adjacentSwappedDatum j h (mergeSlot d j h)).induced.representation) :=
    SegmentProductDatum.inducedEquivOfBlockListEq _ _ (congrArg SegmentProductDatum.blockList
      (d.adjacentSwappedDatum_merged_eq j h).symm)
  have q' := (d.adjacentSwappedInducedEquiv j h).symm
  have key := exists_injective_of_refinement_slot_two_layers T d (mergeShape d j h)
      (mergeRefinement d j h) (mergeLabel d j h) (mergeLabel_size d j h)
      (d.shape.adjacent_index j h) (mergeSlot d j h) s i i' hii
      (fun k => (d.adjacentReplacementDatum j h e₂ k).induced.representation)
      (fun k => (d.adjacentSwappedDatum j h k).induced.representation)
      a (b.toIntertwiningMap.comp ε.toIntertwiningMap)
      (b.injective.comp ε.injective)
      a' (b'.toIntertwiningMap.comp g) (b'.injective.comp hg)
      π.representation hπ f hf
  rcases key with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · refine Or.inr ⟨U, I, d.replaceAdjacentSlot j h e₂, hUI.1, hUI.2, ?_,
      d.replaceAdjacentSlot_hasSegmentSocles j h e₂ hd he₂, hπ,
      q.toIntertwiningMap.comp φ, q.injective.comp hφ⟩
    rw [d.replaceAdjacentSlot_segments j h e₂, hlist]
    simp
  · exact Or.inl ⟨hπ, q'.toIntertwiningMap.comp φ, q'.injective.comp hφ⟩

/-- Ze80 §6.7: an irreducible subrepresentation of a segment-socle product with an
adjacent linked pair `Δ' ≺ Δ` embeds into the product with the pair swapped or
into the product with the pair replaced by its union and intersection. -/
theorem linkedSegmentSocleEmbeddingReduction :
    LinkedSegmentSocleEmbeddingReduction.{uF, uV} F T :=
  linkedSegmentSocleEmbeddingReduction_of_gluing F T (linkedSegmentSocleGluing F T)

end Langlands.Classification
