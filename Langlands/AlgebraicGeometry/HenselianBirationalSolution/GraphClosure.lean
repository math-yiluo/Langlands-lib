import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Translations
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.BirationalZMT
import Langlands.AlgebraicGeometry.SmoothReducedBase

/-! # The closure of the graph of `σ⁻¹ ∘ τ` for two translations

For translations `τ`, `σ` of a birational group law, the birational map `σ⁻¹ ∘ τ` is defined on
the open `overlap τ σ` of points `x` of the domain of `τ` with `τ x` in the image of `σ`. The
scheme-theoretic image `graphImage τ σ` of its graph in `Y ×_S Y` is the closure of the graph.
This module sets up these objects; the projections of the closure are shown to be open
immersions in `GraphInjective`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
theorem isReduced_image {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  have (z : f.image) : _root_.IsReduced (f.image.presheaf.stalk z) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.imageι z)) isOpen_univ
    let V : f.image.Opens := f.imageι ⁻¹ᵁ U
    have hV : IsAffineOpen V := hU.preimage f.imageι
    have : _root_.IsReduced Γ(f.image, V) :=
      isReduced_of_injective _ (Scheme.Hom.toImage_app_injective f ⟨U, hU⟩)
    have : _root_.IsReduced Γ(V.toScheme, ⊤) :=
      isReduced_of_injective _ (V.topIso).commRingCatIsoToRingEquiv.injective
    have : IsAffine V.toScheme := hV
    have : IsReduced V.toScheme := isReduced_of_isAffine_isReduced _
    have := isReduced_stalk_of_isReduced (X := V.toScheme) ⟨z, hzU⟩
    exact isReduced_of_injective _
      (V.stalkIso ⟨z, hzU⟩).symm.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

namespace Translation

variable (τ σ : Translation m)

/-- The points `x` of the domain of `τ` with `τ x` in the image of `σ`. -/
def overlap : Y.Opens := τ.dom.ι ''ᵁ (τ.map ⁻¹ᵁ σ.map.opensRange)

theorem overlap_le : overlap τ σ ≤ τ.dom := by
  rintro _ ⟨d, -, rfl⟩
  exact d.2

/-- The inclusion of the overlap into the domain of `τ`. -/
abbrev overlapIncl : (overlap τ σ).toScheme ⟶ τ.dom.toScheme := Y.homOfLE (overlap_le τ σ)

theorem range_overlapIncl_map : Set.range (overlapIncl τ σ ≫ τ.map) ⊆ Set.range σ.map := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨d, hd, hdx⟩ := x.2
  have hx : overlapIncl τ σ x = d := by
    apply τ.dom.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact hdx.symm
  rw [Scheme.Hom.comp_apply, hx]
  exact hd

/-- The birational map `σ⁻¹ ∘ τ` on the overlap. -/
def trans : (overlap τ σ).toScheme ⟶ Y :=
  IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map) (range_overlapIncl_map τ σ) ≫ σ.dom.ι

theorem trans_map : IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map)
    (range_overlapIncl_map τ σ) ≫ σ.map = overlapIncl τ σ ≫ τ.map :=
  IsOpenImmersion.lift_fac _ _ _

theorem trans_comp_g : trans τ σ ≫ g = (overlap τ σ).ι ≫ g := by
  rw [trans, Category.assoc, ← σ.map_comp, reassoc_of% trans_map, τ.map_comp,
    Scheme.homOfLE_ι_assoc]

/-- The graph of `σ⁻¹ ∘ τ`. -/
def graph : (overlap τ σ).toScheme ⟶ pullback g g :=
  pullback.lift (overlap τ σ).ι (trans τ σ) (trans_comp_g τ σ).symm

@[reassoc (attr := simp)]
theorem graph_fst : graph τ σ ≫ pullback.fst g g = (overlap τ σ).ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd : graph τ σ ≫ pullback.snd g g = trans τ σ := pullback.lift_snd _ _ _

instance : IsImmersion (graph τ σ) := by
  have : IsImmersion (graph τ σ ≫ pullback.fst g g) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst g g)

instance [IsNoetherian Y] : QuasiCompact (graph τ σ) := by
  have : TopologicalSpace.NoetherianSpace (overlap τ σ).toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (overlap τ σ : Set Y))
  infer_instance

/-- The closure of the graph of `σ⁻¹ ∘ τ`. -/
abbrev graphImage : Scheme.{u} := (graph τ σ).image

/-- The first projection of the closure of the graph. -/
abbrev pr₁ : graphImage τ σ ⟶ Y := (graph τ σ).imageι ≫ pullback.fst g g

/-- The second projection of the closure of the graph. -/
abbrev pr₂ : graphImage τ σ ⟶ Y := (graph τ σ).imageι ≫ pullback.snd g g

@[reassoc (attr := simp)]
theorem toImage_pr₁ : (graph τ σ).toImage ≫ pr₁ τ σ = (overlap τ σ).ι := by
  rw [Scheme.Hom.toImage_imageι_assoc, graph_fst]

@[reassoc (attr := simp)]
theorem toImage_pr₂ : (graph τ σ).toImage ≫ pr₂ τ σ = trans τ σ := by
  rw [Scheme.Hom.toImage_imageι_assoc, graph_snd]

theorem pr₁_comp_g : pr₁ τ σ ≫ g = pr₂ τ σ ≫ g := by
  simp only [Category.assoc, pullback.condition]

/-- The lift of `τ` on the overlap into the domain of `σ`. -/
abbrev transLift : (overlap τ σ).toScheme ⟶ σ.dom.toScheme :=
  IsOpenImmersion.lift σ.map (overlapIncl τ σ ≫ τ.map) (range_overlapIncl_map τ σ)

theorem range_trans_subset : Set.range (trans τ σ) ⊆ Set.range (overlap σ τ).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, trans, Scheme.Hom.comp_apply]
  refine ⟨transLift τ σ x, ?_, rfl⟩
  change σ.map (transLift τ σ x) ∈ Set.range τ.map
  rw [← Scheme.Hom.comp_apply, trans_map, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- `σ⁻¹ ∘ τ` as a map from the overlap of `τ` with `σ` to the overlap of `σ` with `τ`. -/
def transOverlap : (overlap τ σ).toScheme ⟶ (overlap σ τ).toScheme :=
  IsOpenImmersion.lift (overlap σ τ).ι (trans τ σ) (range_trans_subset τ σ)

@[reassoc (attr := simp)]
theorem transOverlap_ι : transOverlap τ σ ≫ (overlap σ τ).ι = trans τ σ :=
  IsOpenImmersion.lift_fac _ _ _

theorem transOverlap_incl : transOverlap τ σ ≫ overlapIncl σ τ = transLift τ σ := by
  rw [← cancel_mono σ.dom.ι, Category.assoc, Scheme.homOfLE_ι, transOverlap_ι]
  rfl

/-- `τ⁻¹ ∘ σ ∘ σ⁻¹ ∘ τ` is the identity on the overlap. -/
theorem transOverlap_trans : transOverlap τ σ ≫ trans σ τ = (overlap τ σ).ι := by
  have h : transOverlap τ σ ≫ transLift σ τ = overlapIncl τ σ := by
    rw [← cancel_mono τ.map, Category.assoc, trans_map, ← Category.assoc, transOverlap_incl,
      trans_map]
  rw [trans, ← Category.assoc, h, Scheme.homOfLE_ι]

/-- Swapping the factors maps the graph of `σ⁻¹ ∘ τ` onto the graph of `τ⁻¹ ∘ σ`. -/
theorem graph_swap :
    graph τ σ ≫ (pullbackSymmetry g g).hom = transOverlap τ σ ≫ graph σ τ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, graph_snd, graph_fst,
      transOverlap_ι]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, graph_fst, graph_snd,
      transOverlap_trans]

theorem image_swap_range_graph :
    (pullbackSymmetry g g).hom '' Set.range (graph τ σ) ⊆ Set.range (graph σ τ) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨transOverlap τ σ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← graph_swap, Scheme.Hom.comp_apply]

theorem overlap_self : overlap τ τ = τ.dom := by
  apply le_antisymm (overlap_le τ τ)
  intro x hx
  exact ⟨⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩

theorem trans_self : trans τ τ = (overlap τ τ).ι := by
  have h : transLift τ τ = overlapIncl τ τ := by
    rw [← cancel_mono τ.map, trans_map]
  show transLift τ τ ≫ τ.dom.ι = _
  rw [h, Scheme.homOfLE_ι]

theorem dense_dom : Dense (τ.dom : Set Y) := FibreGenerizationDense.dense τ.dom_dense

end Translation

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
