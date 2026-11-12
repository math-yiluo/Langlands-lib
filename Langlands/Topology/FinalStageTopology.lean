import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Bases

/-!
# Final topologies of directed systems of stages

A type `Y` with maps `s i : X i → Y` from topological spaces carries the final topology
`⨆ i, coinduced (s i)`. This module proves the facts used for adelic points:

* a map out of `Y` is continuous when its composites with all stages are;
* if the stages are injective and the transitions of a directed system are open
  embeddings, every stage is an open embedding;
* an injective map `f : Y → Y'` of final topologies, compatible with closed embeddings of the
  stages and with stage-wise saturation, is a closed embedding;
* a bijection compatible with stage-wise homeomorphisms is a homeomorphism.
-/

universe u v w

open Topology Set

namespace Langlands.Topology.FinalStage

variable {ι : Type u} {X : ι → Type v} [τ : ∀ i, TopologicalSpace (X i)] {Y : Type w}

/-- The final topology for a family of maps. -/
abbrev final (s : ∀ i, X i → Y) : TopologicalSpace Y :=
  ⨆ i, TopologicalSpace.coinduced (s i) (τ i)

variable (s : ∀ i, X i → Y)

theorem isOpen_final_iff {U : Set Y} : IsOpen[final s] U ↔ ∀ i, IsOpen (s i ⁻¹' U) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem isClosed_final_iff {C : Set Y} : IsClosed[final s] C ↔ ∀ i, IsClosed (s i ⁻¹' C) := by
  simp only [isClosed_iSup_iff, isClosed_coinduced]

theorem continuous_stage (i : ι) : Continuous[τ i, final s] (s i) :=
  continuous_iSup_rng (continuous_coinduced_rng (t := τ i))

theorem continuous_final_iff {Z : Type*} [TopologicalSpace Z] {g : Y → Z} :
    Continuous[final s, _] g ↔ ∀ i, Continuous (g ∘ s i) := by
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

/-- **Stages are open embeddings** when they are injective and the transitions of the directed
system are open embeddings. -/
theorem isOpenEmbedding_stage [Preorder ι] [IsDirected ι (· ≤ ·)]
    (t : ∀ {i j : ι}, i ≤ j → X i → X j) (ht : ∀ {i j : ι} (h : i ≤ j), IsOpenEmbedding (t h))
    (hst : ∀ {i j : ι} (h : i ≤ j) (x : X i), s j (t h x) = s i x)
    (hinj : ∀ i, Function.Injective (s i)) (i : ι) :
    @IsOpenEmbedding _ _ (τ i) (final s) (s i) := by
  let _ : TopologicalSpace Y := final s
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_stage s i) (hinj i) ?_
  intro U hU
  rw [isOpen_final_iff]
  intro j
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hpre : s j ⁻¹' (s i '' U) = t hjk ⁻¹' (t hik '' U) := by
    ext y
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨u, hu, hsu⟩
      refine ⟨u, hu, hinj k ?_⟩
      rw [hst, hst, hsu]
    · rintro ⟨u, hu, htu⟩
      refine ⟨u, hu, ?_⟩
      rw [← hst hik u, htu, hst]
  rw [hpre]
  exact ((ht hik).isOpenMap U hU).preimage (ht hjk).continuous

variable {X' : ι → Type*} [τ' : ∀ i, TopologicalSpace (X' i)] {Y' : Type*} (s' : ∀ i, X' i → Y')

/-- A map between final topologies is continuous when it is continuous on stages. -/
theorem continuous_of_stages (f : Y → Y') (fs : ∀ i, X i → X' i) (hfs : ∀ i, Continuous (fs i))
    (hcomm : ∀ i x, f (s i x) = s' i (fs i x)) : Continuous[final s, final s'] f := by
  let _ : TopologicalSpace Y' := final s'
  rw [continuous_final_iff]
  intro i
  have : f ∘ s i = s' i ∘ fs i := funext (hcomm i)
  rw [this]
  exact (continuous_stage s' i).comp (hfs i)

/-- **Closed embeddings from stages.** An injective map of final topologies, compatible with
stage-wise closed embeddings, is a closed embedding when a stage point whose image lies in the
image of `f` lies in the image of the stage map. -/
theorem isClosedEmbedding_of_stages (f : Y → Y') (fs : ∀ i, X i → X' i)
    (hfs : ∀ i, IsClosedEmbedding (fs i)) (hcomm : ∀ i x, f (s i x) = s' i (fs i x))
    (hf : Function.Injective f)
    (hsat : ∀ i (y : X' i), s' i y ∈ range f → y ∈ range (fs i)) :
    @IsClosedEmbedding _ _ (final s) (final s') f := by
  let _ : TopologicalSpace Y := final s
  let _ : TopologicalSpace Y' := final s'
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_of_stages s s' f fs (fun i => (hfs i).continuous) hcomm) hf ?_
  intro C hC
  rw [isClosed_final_iff] at hC ⊢
  intro i
  have hpre : s' i ⁻¹' (f '' C) = fs i '' (s i ⁻¹' C) := by
    ext y
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨c, hc, hfc⟩
      obtain ⟨x, rfl⟩ := hsat i y ⟨c, hfc⟩
      refine ⟨x, ?_, rfl⟩
      have : s i x = c := hf (by rw [hcomm, hfc])
      rw [this]
      exact hc
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s i x, hx, hcomm i x⟩
  rw [hpre]
  exact (hfs i).isClosedMap _ (hC i)

/-- **Homeomorphisms from stages.** A bijection of final topologies, compatible with
stage-wise homeomorphisms, is a homeomorphism. -/
theorem isHomeomorph_of_stages (f : Y → Y') (fs : ∀ i, X i → X' i)
    (hfs : ∀ i, IsHomeomorph (fs i)) (hcomm : ∀ i x, f (s i x) = s' i (fs i x))
    (hf : Function.Bijective f) : @IsHomeomorph _ _ (final s) (final s') f := by
  let _ : TopologicalSpace Y := final s
  let _ : TopologicalSpace Y' := final s'
  refine ⟨continuous_of_stages s s' f fs (fun i => (hfs i).continuous) hcomm, ?_, hf⟩
  intro U hU
  rw [isOpen_final_iff] at hU ⊢
  intro i
  have hpre : s' i ⁻¹' (f '' U) = fs i '' (s i ⁻¹' U) := by
    ext y
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨u, hu, hfu⟩
      obtain ⟨x, rfl⟩ := (hfs i).surjective y
      refine ⟨x, ?_, rfl⟩
      have : s i x = u := hf.1 (by rw [hcomm, hfu])
      rw [this]
      exact hu
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s i x, hx, hcomm i x⟩
  rw [hpre]
  exact (hfs i).isOpenMap _ (hU i)

section Cover

variable {Z : Type*} [TopologicalSpace Z] (u : ∀ i, X i → Z) (hemb : ∀ i, IsOpenEmbedding (u i))
include hemb

/-- A space in which any two points lie in a common open Hausdorff stage is Hausdorff. -/
theorem t2Space_of_stages (hcommon : ∀ z₁ z₂ : Z, ∃ k, ∃ a b : X k, u k a = z₁ ∧ u k b = z₂)
    [∀ i, T2Space (X i)] : T2Space Z := by
  rw [t2Space_iff]
  intro z₁ z₂ hne
  obtain ⟨k, a, b, rfl, rfl⟩ := hcommon z₁ z₂
  have hab : a ≠ b := fun h => hne (by rw [h])
  obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation hab
  exact ⟨u k '' U, u k '' V, (hemb k).isOpenMap U hU, (hemb k).isOpenMap V hV,
    mem_image_of_mem _ ha, mem_image_of_mem _ hb,
    (disjoint_image_iff (hemb k).injective).mpr hUV⟩

/-- A space covered by open locally compact stages is locally compact. -/
theorem locallyCompactSpace_of_stages (hcover : ∀ z : Z, ∃ i, ∃ x : X i, u i x = z)
    [∀ i, LocallyCompactSpace (X i)] : LocallyCompactSpace Z := by
  refine ⟨fun z n hn => ?_⟩
  obtain ⟨i, x, rfl⟩ := hcover z
  have hx : u i ⁻¹' n ∈ 𝓝 x := (hemb i).continuous.continuousAt.preimage_mem_nhds hn
  obtain ⟨c, hc, hcn, hcc⟩ := local_compact_nhds hx
  exact ⟨u i '' c, (hemb i).isOpenMap.image_mem_nhds hc, image_subset_iff.mpr hcn,
    hcc.image (hemb i).continuous⟩

/-- A space covered by countably many open second countable stages is second countable. -/
theorem secondCountableTopology_of_stages [Countable ι]
    (hcover : ∀ z : Z, ∃ i, ∃ x : X i, u i x = z) [∀ i, SecondCountableTopology (X i)] :
    SecondCountableTopology Z := by
  have : ∀ i, SecondCountableTopology (range (u i)) := fun i =>
    (IsOpenQuotientMap.mk rangeFactorization_surjective (hemb i).continuous.rangeFactorization
      ((hemb i).isOpenMap.subtype_mk fun x => mem_range_self x)).secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i => range (u i)) (fun i => (hemb i).isOpen_range) ?_
  refine eq_univ_of_forall fun z => ?_
  obtain ⟨i, x, hx⟩ := hcover z
  exact mem_iUnion.mpr ⟨i, x, hx⟩

/-- **Inducing maps from stages.** Let `Φ : Z → W` be compatible with maps of stages
`Φs i : X i → X' i`, where the stages of `Z` and of `W` are open embeddings, every point of `Z`
lies in a stage, and a point of `Z` whose image lies in a stage of `W` lies in the corresponding
stage of `Z`. If every `Φs i` is inducing, so is `Φ`. -/
theorem isInducing_of_stages {X' : ι → Type*} [∀ i, TopologicalSpace (X' i)] {W : Type*}
    [TopologicalSpace W] (u' : ∀ i, X' i → W) (hemb' : ∀ i, IsOpenEmbedding (u' i))
    (Φ : Z → W) (Φs : ∀ i, X i → X' i) (hΦs : ∀ i, IsInducing (Φs i))
    (hcomm : ∀ i x, Φ (u i x) = u' i (Φs i x))
    (hsat : ∀ i (z : Z), Φ z ∈ range (u' i) → z ∈ range (u i))
    (hcover : ∀ z : Z, ∃ i, ∃ x : X i, u i x = z) : IsInducing Φ := by
  rw [isInducing_iff_nhds]
  intro z
  obtain ⟨i, x, rfl⟩ := hcover z
  have key : ∀ G : Filter (X' i), Filter.comap Φ (Filter.map (u' i) G) =
      Filter.map (u i) (Filter.comap (Φs i) G) := by
    intro G
    ext t
    simp only [Filter.mem_comap, Filter.mem_map]
    constructor
    · rintro ⟨v, hv, hvt⟩
      refine ⟨u' i ⁻¹' v, hv, fun y hy => hvt ?_⟩
      change Φ (u i y) ∈ v
      rw [hcomm]
      exact hy
    · rintro ⟨w, hw, hwt⟩
      refine ⟨u' i '' w, ?_, fun y hy => ?_⟩
      · rwa [Set.preimage_image_eq _ (hemb' i).injective]
      · obtain ⟨a, ha, hay⟩ := hy
        obtain ⟨b, rfl⟩ := hsat i y ⟨a, hay⟩
        have : Φs i b = a := (hemb' i).injective (by rw [← hcomm, hay])
        exact hwt (show Φs i b ∈ w by rw [this]; exact ha)
  rw [← (hemb i).map_nhds_eq, hcomm, ← (hemb' i).map_nhds_eq, key, ← (hΦs i).nhds_eq_comap]

end Cover

end Langlands.Topology.FinalStage
