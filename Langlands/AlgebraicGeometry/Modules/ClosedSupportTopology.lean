import Mathlib.Topology.KrullDimension

/-! # Heights of irreducible closed sets under closed embeddings -/

noncomputable section

open TopologicalSpace Topology Order

namespace Langlands.AlgebraicGeometry.Modules.ClosedSupportTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An irreducible closed subset contained in an embedding's range lifts to
an irreducible closed subset of its source. -/
theorem exists_map_eq {f : X → Y} (hf : IsEmbedding f)
    (T : IrreducibleCloseds Y) (hT : (T : Set Y) ⊆ Set.range f) :
    ∃ S : IrreducibleCloseds X, IrreducibleCloseds.map f hf.continuous S = T := by
  let : IrreducibleSpace (T : Set Y) := Subtype.irreducibleSpace T.isIrreducible
  let : IrreducibleSpace (f ⁻¹' (T : Set Y)) :=
    (hf.homeomorphOfSubsetRange hT).irreducibleSpace_iff.mpr inferInstance
  refine ⟨⟨f ⁻¹' (T : Set Y), IsIrreducible.of_subtype,
    T.isClosed.preimage hf.continuous⟩, ?_⟩
  apply IrreducibleCloseds.ext
  change closure (f '' (f ⁻¹' (T : Set Y))) = (T : Set Y)
  rw [Set.image_preimage_eq_of_subset hT, T.isClosed.closure_eq]

/-- A closed embedding preserves the height of every irreducible closed set. -/
theorem height_map {f : X → Y} (hf : IsClosedEmbedding f)
    (S : IrreducibleCloseds X) :
    height (IrreducibleCloseds.map f hf.continuous S) = height S := by
  symm
  apply Order.height_eq_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing)
  intro A B hBA
  have hB : (B : Set Y) ⊆ Set.range f := by
    intro y hy
    have hyA := hBA.le hy
    change y ∈ closure (f '' (A : Set X)) at hyA
    rw [(hf.isClosedMap _ A.isClosed).closure_eq] at hyA
    exact Set.image_subset_range _ _ hyA
  obtain ⟨C, hC⟩ := exists_map_eq hf.isEmbedding B hB
  refine ⟨C, ?_, hC⟩
  apply lt_of_le_of_ne
  · intro x hx
    have hfx : f x ∈ (IrreducibleCloseds.map f hf.continuous C : Set Y) :=
      subset_closure ⟨x, hx, rfl⟩
    rw [hC] at hfx
    have hxA := hBA.le hfx
    change f x ∈ closure (f '' (A : Set X)) at hxA
    rw [(hf.isClosedMap _ A.isClosed).closure_eq] at hxA
    obtain ⟨x', hx', heq⟩ := hxA
    exact hf.injective heq ▸ hx'
  · intro h
    subst C
    exact hBA.ne hC.symm

/-- A closed subspace has dimension less than a natural bound exactly when
all its ambient irreducible closed subsets have height less than that bound. -/
theorem topologicalKrullDim_lt_iff (Z : Closeds X) (e : ℕ) :
    topologicalKrullDim (Z : Set X) < (e : WithBot ℕ∞) ↔
      ∀ T : IrreducibleCloseds X, (T : Set X) ⊆ Z → height T < e := by
  let i : ↥(Z : Set X) → X := Subtype.val
  have hi : IsClosedEmbedding i := Z.isClosed.isClosedEmbedding_subtypeVal
  constructor
  · intro h T hT
    have hTr : (T : Set X) ⊆ Set.range i := by
      simpa only [i, Subtype.range_coe] using hT
    obtain ⟨S, hS⟩ := exists_map_eq hi.isEmbedding T hTr
    have hheight := height_map hi S
    rw [hS] at hheight
    rw [hheight]
    exact WithBot.coe_lt_coe.mp ((Order.height_le_krullDim S).trans_lt h)
  · intro h
    apply Order.krullDim_lt_coe_iff.mpr
    intro p
    have hsub : (IrreducibleCloseds.map i hi.continuous p.last : Set X) ⊆ Z := by
      change closure (i '' (p.last : Set (Z : Set X))) ⊆ Z
      apply closure_minimal _ Z.isClosed
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    have hh := h _ hsub
    rw [height_map hi] at hh
    exact_mod_cast (Order.length_le_height_last (p := p)).trans_lt hh

end Langlands.AlgebraicGeometry.Modules.ClosedSupportTopology
