/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.CommonModification
public import WeilConjectures.Compactification.TwoOpenComparison
public import WeilConjectures.Compactification.ValuativeCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!

# The two-open compactification theorem

This file assembles the **two-open compactification theorem** (Stacks Project
Tag 0F40; blueprint chapter "Nagata compactification", section "The two-open
compactification theorem", proof order items 43–48): over a Noetherian base `S`, a
separated finite-type morphism `u : U ⟶ S` is compactifiable as soon as `U` is covered
by two compactifiable opens with dense intersection
(`AlgebraicGeometry.HasCompactification.of_two_open_cover`).

The intermediate schemes of the construction are built from a prepared side
`σ : TwoOpenSide u O`:

- `AlgebraicGeometry.TwoOpenSide.intermediate`: the glued scheme
  `Wᵢ = U ⊔_{O} Xᵢ°` obtained by gluing `U` and the complement `Xᵢ°` of the forbidden
  boundary along the embedded copy of `O` (blueprint:
  `proposition-compactifying-union-two-opens--1`; proof order item 43), with its two
  charts `intermediateU`, `intermediateInterior` and structure morphism
  `intermediateHom`;
- `AlgebraicGeometry.TwoOpenSide.isConstructible_range_intermediateGraph` and
  `AlgebraicGeometry.TwoOpenSide.stableUnderSpecialization_range_intermediateGraph`: the
  image of the overlap `O ⟶ U ×_S Xᵢ°` is constructible (Chevalley) and stable under
  specialization, the latter via
  `AlgebraicGeometry.TwoOpenSide.exists_graph_eq_of_specializes` (blueprint:
  `proposition-compactifying-union-two-opens--1`,
  `lemma-nagata-intermediate-specialization-boundary`,
  `lemma-nagata-intermediate-overlap-specialization-closed`);
- `AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph`: the overlap
  `O ⟶ U ×_S Xᵢ°` is a closed immersion — its range is the preimage of the closed
  range of the proper graph `V ⟶ U ×_S X` (blueprint:
  `proposition-compactifying-union-two-opens--1`,
  `lemma-nagata-intermediate-overlap-closed`; this exact description of the range makes
  the closedness hold without Noetherian hypotheses);
- `AlgebraicGeometry.TwoOpenSide.isSeparated_intermediateHom`: `Wᵢ ⟶ S` is separated
  (Stacks Project Tag 0F3U via `IsSeparated.pushout_desc`; blueprint:
  `proposition-compactifying-union-two-opens--1`);
- `AlgebraicGeometry.TwoOpenSide.dense_range_intermediateU`: the copy of `U` is dense
  in `Wᵢ` (blueprint: part of `proposition-compactifying-union-two-opens--1`);
- `AlgebraicGeometry.TwoOpenSide.intermediateLift`: a morphism to the ambient model
  avoiding the forbidden boundary lifts to `Wᵢ` (blueprint: second half of
  `proposition-compactifying-union-two-opens--1`).

The final modification is the common modification (Stacks Project Tag 0F3X) of `W₁`,
`W₂`, `AlgebraicGeometry.TwoOpenPreparation.FinalModification` (blueprint:
`proposition-compactifying-union-two-opens--1`;
item 45; a chosen one is `TwoOpenPreparation.finalModification`, and its structural
properties are collected in `TwoOpenPreparation.FinalModification.spec`), with the open
immersion `CommonModification.j : U ⟶ W` (blueprint:
`proposition-compactifying-union-two-opens--1`). On it:

- `TwoOpenPreparation.FinalModification.isDominant`: `O₁ ∩ O₂ ⟶ W` is dominant
  (blueprint: `proposition-compactifying-union-two-opens--1`;
  items 46–47);
- `TwoOpenPreparation.FinalModification.valuativeCriterion_relativeTo`: valuative squares
  through `O₁ ∩ O₂` lift uniquely, using the proper valuative criterion of the sides and
  the boundary avoidance of the comparison layer (blueprint:
  `proposition-compactifying-union-two-opens--1`,
  `lemma-nagata-two-open-valuative-lifting`; item 44);
- `TwoOpenPreparation.FinalModification.isProper_w`: `W ⟶ S` is proper by the dense-source
  valuative criterion (Stacks Project Tag 0894,
  `UniversallyClosed.of_valuativeCriterion_of_isDominant`; blueprint:
  `proposition-compactifying-union-two-opens--1`);
- `TwoOpenPreparation.FinalModification.compactification` and
  `HasCompactification.of_two_open_cover`: the resulting compactification (blueprint:
  `proposition-compactifying-union-two-opens--1`; item 48).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

namespace TwoOpenSide

variable {u : U ⟶ S} {O : U.Opens} (σ : TwoOpenSide u O)

section Intermediate

lemma interiorEmb_comm : O.ι ≫ u = σ.interiorEmb ≫ σ.interior.ι ≫ σ.s := by
  rw [σ.interiorEmb_ι_assoc, σ.embX_s]

/-- The **intermediate scheme** `Wᵢ = U ⊔_O Xᵢ°` of a side: the gluing of `U` and the
complement of the forbidden boundary along the embedded copy of `O`.
(Blueprint: `proposition-compactifying-union-two-opens--1`; proof order item 43.) -/
def intermediate : Scheme.{u} := pushout O.ι σ.interiorEmb

/-- The chart `U ⟶ Wᵢ` of the intermediate scheme. -/
def intermediateU : U ⟶ σ.intermediate := pushout.inl O.ι σ.interiorEmb

/-- The chart `Xᵢ° ⟶ Wᵢ` of the intermediate scheme. -/
def intermediateInterior : σ.interior.toScheme ⟶ σ.intermediate :=
  pushout.inr O.ι σ.interiorEmb

instance : IsOpenImmersion σ.intermediateU :=
  inferInstanceAs (IsOpenImmersion (pushout.inl O.ι σ.interiorEmb))

instance : IsOpenImmersion σ.intermediateInterior :=
  inferInstanceAs (IsOpenImmersion (pushout.inr O.ι σ.interiorEmb))

@[reassoc]
lemma intermediate_condition :
    O.ι ≫ σ.intermediateU = σ.interiorEmb ≫ σ.intermediateInterior :=
  pushout.condition

/-- The structure morphism `Wᵢ ⟶ S` of the intermediate scheme. -/
def intermediateHom : σ.intermediate ⟶ S :=
  pushout.desc u (σ.interior.ι ≫ σ.s) σ.interiorEmb_comm

@[reassoc (attr := simp)]
lemma intermediateU_hom : σ.intermediateU ≫ σ.intermediateHom = u :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma intermediateInterior_hom :
    σ.intermediateInterior ≫ σ.intermediateHom = σ.interior.ι ≫ σ.s :=
  pushout.inr_desc _ _ _

lemma range_intermediateU_union :
    Set.range σ.intermediateU ∪ Set.range σ.intermediateInterior = Set.univ :=
  range_pushout_inl_union_range_pushout_inr O.ι σ.interiorEmb

/-- **The copy of `U` is dense in the intermediate scheme**: the second chart is the
complement of the forbidden boundary, in which the embedded copy of `O` is dense.
(Blueprint: part of `proposition-compactifying-union-two-opens--1`.) -/
theorem dense_range_intermediateU : Dense (Set.range σ.intermediateU) := by
  rw [dense_iff_inter_open]
  rintro W₀ hW₀ ⟨w₀, hw₀⟩
  have hw₀cov : w₀ ∈ Set.range σ.intermediateU ∪ Set.range σ.intermediateInterior := by
    rw [σ.range_intermediateU_union]
    trivial
  obtain ⟨a, rfl⟩ | ⟨p, rfl⟩ := hw₀cov
  · exact ⟨σ.intermediateU a, hw₀, a, rfl⟩
  · -- transport the open to `X` and use density of the copy of `O`
    have hopen : IsOpen (σ.interior.ι '' (σ.intermediateInterior ⁻¹' W₀)) :=
      σ.interior.ι.isOpenEmbedding.isOpenMap _
        (hW₀.preimage σ.intermediateInterior.continuous)
    obtain ⟨d, hd, hdD⟩ := dense_iff_inter_open.mp σ.dense_range_embX _ hopen
      ⟨σ.interior.ι p, ⟨p, hw₀, rfl⟩⟩
    obtain ⟨q, hq, hqd⟩ := hd
    obtain ⟨o, rfl⟩ := hdD
    have hqEmb : q = σ.interiorEmb o := by
      apply σ.interior.ι.isOpenEmbedding.injective
      rw [hqd]
      exact congrArg (fun m ↦ m) (by rw [← σ.interiorEmb_ι]; exact Scheme.Hom.comp_apply _ _ _)
    refine ⟨σ.intermediateInterior q, ?_, ?_⟩
    · exact hq
    · refine ⟨O.ι o, ?_⟩
      rw [hqEmb, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        σ.intermediate_condition]

section Graph

/-- The proper graph `γ : V ⟶ U ×_S X` of the proper extension `ψ`.
(Blueprint: `proposition-compactifying-union-two-opens--1`.) -/
def graph : σ.V.toScheme ⟶ pullback u σ.s := pullback.lift σ.ψ σ.V.ι σ.ψ_u

@[reassoc (attr := simp)]
lemma graph_fst : σ.graph ≫ pullback.fst u σ.s = σ.ψ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_snd : σ.graph ≫ pullback.snd u σ.s = σ.V.ι := pullback.lift_snd _ _ _

/-- The graph of the proper extension is proper; in particular its range is closed.
(Blueprint: `proposition-compactifying-union-two-opens--1`.) -/
theorem isProper_graph : IsProper σ.graph := by
  have := σ.isProper_ψ
  have := σ.isProper_s
  have : IsProper (σ.graph ≫ pullback.fst u σ.s) := by
    rw [σ.graph_fst]
    exact σ.isProper_ψ
  exact IsProper.of_comp σ.graph (pullback.fst u σ.s)

/-- The open immersion `U ×_S Xᵢ° ⟶ U ×_S X` induced by the inclusion of the
complement of the forbidden boundary. -/
def intermediateOpenι : pullback u (σ.interior.ι ≫ σ.s) ⟶ pullback u σ.s :=
  pullback.map u (σ.interior.ι ≫ σ.s) u σ.s (𝟙 U) σ.interior.ι (𝟙 S) (by simp) (by simp)

instance : IsOpenImmersion σ.intermediateOpenι :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (by simp) rfl

@[reassoc (attr := simp)]
lemma intermediateOpenι_fst :
    σ.intermediateOpenι ≫ pullback.fst u σ.s = pullback.fst u (σ.interior.ι ≫ σ.s) ≫ 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma intermediateOpenι_snd :
    σ.intermediateOpenι ≫ pullback.snd u σ.s =
      pullback.snd u (σ.interior.ι ≫ σ.s) ≫ σ.interior.ι :=
  pullback.lift_snd _ _ _

/-- The overlap map `O ⟶ U ×_S Xᵢ°` of the two charts of the intermediate scheme. -/
def intermediateGraph : O.toScheme ⟶ pullback u (σ.interior.ι ≫ σ.s) :=
  pullback.lift O.ι σ.interiorEmb σ.interiorEmb_comm

@[reassoc (attr := simp)]
lemma intermediateGraph_fst :
    σ.intermediateGraph ≫ pullback.fst u (σ.interior.ι ≫ σ.s) = O.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma intermediateGraph_snd :
    σ.intermediateGraph ≫ pullback.snd u (σ.interior.ι ≫ σ.s) = σ.interiorEmb :=
  pullback.lift_snd _ _ _

lemma intermediateGraph_openι :
    σ.intermediateGraph ≫ σ.intermediateOpenι = σ.υ ≫ σ.graph := by
  apply pullback.hom_ext
  · rw [Category.assoc, σ.intermediateOpenι_fst, σ.intermediateGraph_fst_assoc,
      Category.comp_id, Category.assoc, σ.graph_fst, σ.υ_ψ]
  · rw [Category.assoc, σ.intermediateOpenι_snd, σ.intermediateGraph_snd_assoc,
      σ.interiorEmb_ι, Category.assoc, σ.graph_snd]
    rfl

/-- **A specialization of the overlap stays on the graph** (blueprint:
`proposition-compactifying-union-two-opens--1`): if a point of the image of `O` in
`U ×_S X` specializes to `t'`, then `t'` is a graph point `γ(v)`, and if its first
coordinate leaves `O`, then its second coordinate lies in the forbidden boundary. -/
theorem exists_graph_eq_of_specializes {t t' : ↥(pullback u σ.s)}
    (ht : t ∈ Set.range (σ.υ ≫ σ.graph)) (h : t ⤳ t') :
    ∃ v, σ.graph v = t' ∧
      (pullback.fst u σ.s t' ∉ (O : Set U) → pullback.snd u σ.s t' ∈ σ.forbiddenBoundary) := by
  have := σ.isProper_graph
  have hmem : t' ∈ Set.range σ.graph := by
    obtain ⟨o, rfl⟩ := ht
    exact h.mem_closed σ.graph.isClosedMap.isClosed_range ⟨σ.υ o, by
      rw [Scheme.Hom.comp_apply]⟩
  obtain ⟨v, rfl⟩ := hmem
  refine ⟨v, rfl, fun hv ↦ subset_closure ⟨v, ?_, ?_⟩⟩
  · rwa [← Scheme.Hom.comp_apply, σ.graph_fst] at hv
  · rw [← Scheme.Hom.comp_apply, σ.graph_snd]

/-- **The overlap image is stable under specialization** (blueprint:
`proposition-compactifying-union-two-opens--1`): a specialization of a point of
the image of `O` in `U ×_S Xᵢ°` is a graph point lying over `O`, since its second
coordinate avoids the forbidden boundary; it is therefore again in the image of `O`. -/
theorem stableUnderSpecialization_range_intermediateGraph :
    StableUnderSpecialization (Set.range σ.intermediateGraph) := by
  have := σ.isOpenImmersion_υ
  rintro - t' h ⟨o, rfl⟩
  obtain ⟨v, hv, hbd⟩ := σ.exists_graph_eq_of_specializes
    ⟨o, by rw [← σ.intermediateGraph_openι, Scheme.Hom.comp_apply]⟩
    (h.map σ.intermediateOpenι.continuous)
  have hsnd : pullback.snd u σ.s (σ.intermediateOpenι t') ∈ (σ.interior : Set σ.X) := by
    rw [← Scheme.Hom.comp_apply, σ.intermediateOpenι_snd, Scheme.Hom.comp_apply,
      ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have hvO : v ∈ Set.range σ.υ := by
    rw [σ.range_υ, Set.mem_preimage, ← σ.graph_fst, Scheme.Hom.comp_apply, hv]
    by_contra hn
    exact hsnd (hbd hn)
  obtain ⟨o', rfl⟩ := hvO
  refine ⟨o', σ.intermediateOpenι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, σ.intermediateGraph_openι, Scheme.Hom.comp_apply, hv]

/-- **The overlap image is constructible** (blueprint:
`proposition-compactifying-union-two-opens--1`): over a Noetherian base, the overlap
map is a morphism of finite presentation between Noetherian schemes, so Chevalley's
theorem applies. -/
theorem isConstructible_range_intermediateGraph [IsNoetherian S] [LocallyOfFiniteType u]
    [QuasiCompact u] : Topology.IsConstructible (Set.range σ.intermediateGraph) := by
  have := σ.isProper_s
  have : IsNoetherian σ.X := σ.isNoetherian_X
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : IsNoetherian U := ⟨⟩
  have : CompactSpace O.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian O.toScheme := ⟨⟩
  have : CompactSpace σ.interior.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian σ.interior.toScheme := ⟨⟩
  have : IsLocallyNoetherian (pullback u (σ.interior.ι ≫ σ.s)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst u (σ.interior.ι ≫ σ.s) ≫ u)
  have : CompactSpace ↥(pullback u (σ.interior.ι ≫ σ.s)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst u (σ.interior.ι ≫ σ.s))
  have : IsNoetherian (pullback u (σ.interior.ι ≫ σ.s)) := ⟨⟩
  have : LocallyOfFinitePresentation
      (σ.intermediateGraph ≫ pullback.fst u (σ.interior.ι ≫ σ.s)) := by
    rw [σ.intermediateGraph_fst]
    infer_instance
  have := locallyOfFinitePresentation_of_comp σ.intermediateGraph
    (pullback.fst u (σ.interior.ι ≫ σ.s))
  rw [← Set.image_univ]
  exact σ.intermediateGraph.isConstructible_image Topology.IsConstructible.univ

/-- **The overlap of the two charts of the intermediate scheme is a closed immersion**
(blueprint: `proposition-compactifying-union-two-opens--1`).

The range of the overlap map is the preimage of the closed range of the proper graph
`V ⟶ U ×_S X`, because over the complement of the forbidden boundary the graph passes
through the embedded copy of `O` exactly over `O` (`TwoOpenSide.range_υ`). -/
theorem isClosedImmersion_intermediateGraph :
    IsClosedImmersion σ.intermediateGraph := by
  have := σ.isOpenImmersion_υ
  have hprop := σ.isProper_graph
  -- the overlap map is an immersion since its first projection is an open immersion
  have : IsImmersion (σ.intermediateGraph ≫ pullback.fst u (σ.interior.ι ≫ σ.s)) := by
    rw [σ.intermediateGraph_fst]
    infer_instance
  have : IsImmersion σ.intermediateGraph :=
    IsImmersion.of_comp σ.intermediateGraph (pullback.fst u (σ.interior.ι ≫ σ.s))
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  -- the range is the preimage of the closed range of the proper graph
  · have hkey : Set.range σ.intermediateGraph =
        σ.intermediateOpenι ⁻¹' (Set.range σ.graph) := by
      apply subset_antisymm
      · rintro - ⟨o, rfl⟩
        refine Set.mem_preimage.mpr ⟨σ.υ o, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← σ.intermediateGraph_openι, Scheme.Hom.comp_apply]
      · intro t ht
        obtain ⟨v, hv⟩ := Set.mem_preimage.mp ht
        -- the second component of the graph point lies in the interior
        have hvV : σ.V.ι v ∈ (σ.interior : Set σ.X) := by
          have h1 : σ.V.ι v = (σ.graph ≫ pullback.snd u σ.s) v := by
            rw [σ.graph_snd]
          have h2 : (σ.graph ≫ pullback.snd u σ.s) v =
              pullback.snd u σ.s (σ.intermediateOpenι t) := by
            rw [Scheme.Hom.comp_apply, hv]
          have h3 : pullback.snd u σ.s (σ.intermediateOpenι t) =
              σ.interior.ι (pullback.snd u (σ.interior.ι ≫ σ.s) t) := by
            calc pullback.snd u σ.s (σ.intermediateOpenι t)
                = (σ.intermediateOpenι ≫ pullback.snd u σ.s) t :=
                  (Scheme.Hom.comp_apply _ _ _).symm
              _ = (pullback.snd u (σ.interior.ι ≫ σ.s) ≫ σ.interior.ι) t := by
                  rw [σ.intermediateOpenι_snd]
              _ = σ.interior.ι (pullback.snd u (σ.interior.ι ≫ σ.s) t) :=
                  Scheme.Hom.comp_apply _ _ _
          rw [h1, h2, h3, ← Scheme.Opens.range_ι]
          exact ⟨_, rfl⟩
        -- hence the graph point passes through the embedded copy of `O`
        have hvO : v ∈ Set.range σ.υ := by
          rw [σ.range_υ]
          by_contra hvO
          have hvZ : σ.V.ι v ∈ σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)) :=
            ⟨v, fun h ↦ hvO h, rfl⟩
          exact hvV (subset_closure hvZ)
        obtain ⟨o, rfl⟩ := hvO
        refine ⟨o, ?_⟩
        apply σ.intermediateOpenι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, σ.intermediateGraph_openι, Scheme.Hom.comp_apply, hv]
    rw [hkey]
    exact (σ.graph.isClosedMap.isClosed_range).preimage σ.intermediateOpenι.continuous

end Graph

section Structure

/-- **Separatedness of the intermediate scheme** (Stacks Project Tag 0F3U; blueprint:
`proposition-compactifying-union-two-opens--1`): the two charts of `Wᵢ ⟶ S` are separated and
their overlap is a closed immersion. -/
theorem isSeparated_intermediateHom [IsSeparated u] : IsSeparated σ.intermediateHom := by
  have := σ.isProper_s
  have : IsSeparated (σ.interior.ι ≫ σ.s) := inferInstance
  exact IsSeparated.pushout_desc O.ι σ.interiorEmb σ.interiorEmb_comm
    σ.isClosedImmersion_intermediateGraph

/-- The intermediate scheme is of finite type over the base (blueprint:
`proposition-compactifying-union-two-opens--1`, finite-type part). -/
theorem locallyOfFiniteType_intermediateHom [LocallyOfFiniteType u] :
    LocallyOfFiniteType σ.intermediateHom := by
  have := σ.isProper_s
  exact IsZariskiLocalAtSource.pushout_desc O.ι σ.interiorEmb σ.interiorEmb_comm
    inferInstance inferInstance

/-- The intermediate scheme of a side over a Noetherian base is quasi-compact. -/
theorem compactSpace_intermediate [IsNoetherian S] [QuasiCompact u] :
    CompactSpace σ.intermediate := by
  have : IsNoetherian σ.X := σ.isNoetherian_X
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : CompactSpace σ.interior.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  exact inferInstanceAs (CompactSpace ↑(pushout O.ι σ.interiorEmb))

/-- The intermediate scheme of a side over a Noetherian base is Noetherian. -/
theorem isNoetherian_intermediate [IsNoetherian S] [LocallyOfFiniteType u]
    [QuasiCompact u] : IsNoetherian σ.intermediate := by
  have : IsLocallyNoetherian σ.intermediate := by
    have := σ.locallyOfFiniteType_intermediateHom
    exact LocallyOfFiniteType.isLocallyNoetherian σ.intermediateHom
  have := σ.compactSpace_intermediate
  exact ⟨⟩

/-- The morphism to the intermediate scheme determined by a morphism `g` to the ambient
model avoiding the forbidden boundary (blueprint: second half of
`proposition-compactifying-union-two-opens--1`). -/
def intermediateLift {Y : Scheme.{u}} (g : Y ⟶ σ.X)
    (hg : Set.range g ⊆ (σ.interior : Set σ.X)) : Y ⟶ σ.intermediate :=
  IsOpenImmersion.lift σ.interior.ι g (by rwa [Scheme.Opens.range_ι]) ≫
    σ.intermediateInterior

@[reassoc (attr := simp)]
lemma intermediateLift_hom {Y : Scheme.{u}} (g : Y ⟶ σ.X)
    (hg : Set.range g ⊆ (σ.interior : Set σ.X)) :
    σ.intermediateLift g hg ≫ σ.intermediateHom = g ≫ σ.s := by
  rw [intermediateLift, Category.assoc, σ.intermediateInterior_hom,
    IsOpenImmersion.lift_fac_assoc]

/-- The lift to the intermediate scheme extends the copy of `O`: if `g` restricts along
`e` to a morphism `a` into `O`, then so does its lift. -/
lemma comp_intermediateLift {Y Z : Scheme.{u}} (g : Y ⟶ σ.X)
    (hg : Set.range g ⊆ (σ.interior : Set σ.X)) (e : Z ⟶ Y) (a : Z ⟶ O.toScheme)
    (he : e ≫ g = a ≫ σ.embX) :
    e ≫ σ.intermediateLift g hg = a ≫ O.ι ≫ σ.intermediateU := by
  have h : e ≫ IsOpenImmersion.lift σ.interior.ι g (by rwa [Scheme.Opens.range_ι]) =
      a ≫ σ.interiorEmb := by
    rw [← cancel_mono σ.interior.ι, Category.assoc, IsOpenImmersion.lift_fac, he,
      Category.assoc, σ.interiorEmb_ι]
  rw [intermediateLift, ← Category.assoc, h, Category.assoc, σ.intermediate_condition]

end Structure

end Intermediate

end TwoOpenSide

namespace TwoOpenPreparation

variable {O₁ O₂ : U.Opens} {u : U ⟶ S} (P : TwoOpenPreparation u O₁ O₂)

/-- The **final common modification** of the two-open construction (blueprint:
`proposition-compactifying-union-two-opens--1`): a common modification (Stacks Project
Tag 0F3X) of the two intermediate schemes `W₁`, `W₂` along their common open `U`. It
consists of `U`-admissible blow-ups `Wᵢ' ⟶ Wᵢ` glued to a scheme `W` over `S`; the
induced open immersion `U ⟶ W` is `CommonModification.j` (blueprint:
`proposition-compactifying-union-two-opens--1`). -/
abbrev FinalModification : Type (u + 1) :=
  CommonModification P.side₁.intermediateHom P.side₂.intermediateHom
    P.side₁.intermediateU P.side₂.intermediateU

/-- **Existence of the final common modification** (blueprint:
`proposition-compactifying-union-two-opens--1`): the intermediate schemes are separated and of
finite type over `S` (`TwoOpenSide.isSeparated_intermediateHom`), so the common
modification of Stacks Project Tag 0F3X applies. The structural assertions of the lemma
are the fields of `CommonModification`; the open immersion `U ⟶ W` is
`CommonModification.j`. -/
theorem nonempty_finalModification [IsNoetherian S] [IsSeparated u] [LocallyOfFiniteType u]
    [QuasiCompact u] : Nonempty P.FinalModification := by
  have : IsSeparated P.side₁.intermediateHom := P.side₁.isSeparated_intermediateHom
  have : IsSeparated P.side₂.intermediateHom := P.side₂.isSeparated_intermediateHom
  have : LocallyOfFiniteType P.side₁.intermediateHom :=
    P.side₁.locallyOfFiniteType_intermediateHom
  have : LocallyOfFiniteType P.side₂.intermediateHom :=
    P.side₂.locallyOfFiniteType_intermediateHom
  have : IsNoetherian P.side₁.intermediate := P.side₁.isNoetherian_intermediate
  have : IsNoetherian P.side₂.intermediate := P.side₂.isNoetherian_intermediate
  exact nonempty_commonModification P.side₁.intermediateHom P.side₂.intermediateHom
    P.side₁.intermediateU P.side₂.intermediateU
    (by rw [P.side₁.intermediateU_hom, P.side₂.intermediateU_hom])

/-- Blueprint `proposition-compactifying-union-two-opens--1`: Final common modification for the
two-open construction.

The chosen common modification `W = CM(W₁, W₂; U)` of the two intermediate schemes
`Wᵢ = U ⊔_{Oᵢ} Xᵢ°` along their common open `U`: it consists of `U`-admissible blow-ups
`W'ᵢ ⟶ Wᵢ` (`CommonModification.B₁`, `CommonModification.B₂`), open immersions `W'ᵢ ⟶ W`
(`CommonModification.k₁`, `CommonModification.k₂`) and the structure morphism
`W ⟶ S` (`CommonModification.w`). -/
def finalModification [IsNoetherian S] [IsSeparated u] [LocallyOfFiniteType u]
    [QuasiCompact u] : P.FinalModification :=
  Classical.choice P.nonempty_finalModification

namespace FinalModification

variable {P} (cm : P.FinalModification)

@[reassoc (attr := simp)]
lemma j_comp_w : cm.j ≫ cm.w = u := by
  rw [cm.j_w, P.side₁.intermediateU_hom]

/-- Blueprint `proposition-compactifying-union-two-opens--1`: Structural properties of the final
common modification.

For a final common modification `W` of `W₁`, `W₂` (for instance
`TwoOpenPreparation.finalModification`), the blow-ups `W'ᵢ ⟶ Wᵢ` are `U`-admissible (this is
encoded in the types of `cm.B₁ : IsAdmissible W₁ U`, `cm.B₂ : IsAdmissible W₂ U`) and the
lifts of `U` to `W'ᵢ` lie over the open immersions `U ⟶ Wᵢ`; the maps `W'ᵢ ⟶ W` are open
immersions covering `W`; their copies of `U` agree; `W ⟶ S` is separated and of finite type;
and the induced map `j_W : U ⟶ W` is an open immersion over `S`. -/
theorem spec :
    cm.u₁ ≫ cm.B₁.I.blowupMap = P.side₁.intermediateU ∧
      cm.u₂ ≫ cm.B₂.I.blowupMap = P.side₂.intermediateU ∧
      IsOpenImmersion cm.k₁ ∧ IsOpenImmersion cm.k₂ ∧
      Set.range cm.k₁ ∪ Set.range cm.k₂ = Set.univ ∧ cm.u₁ ≫ cm.k₁ = cm.u₂ ≫ cm.k₂ ∧
      IsSeparated cm.w ∧ LocallyOfFiniteType cm.w ∧ QuasiCompact cm.w ∧
      IsOpenImmersion cm.j ∧ cm.j ≫ cm.w = u :=
  ⟨cm.u₁_blowupMap, cm.u₂_blowupMap, inferInstance, inferInstance, cm.cover, cm.u_glue,
    inferInstance, inferInstance, inferInstance, inferInstance, cm.j_comp_w⟩

/-- **Density after the final common modification** (blueprint:
`proposition-compactifying-union-two-opens--1`): the map `O₁ ∩ O₂ ⟶ W` is dominant. The copies of
`U` are dense in the intermediate schemes, density is transported through the common
modification (`CommonModification.dense_range_j`, blueprint
`proposition-compactifying-union-two-opens--1`), and `O₁ ∩ O₂` is dense in `U`. Its
quasi-compactness is automatic, as `O₁ ∩ O₂` is Noetherian. -/
theorem isDominant [IsNoetherian S] [LocallyOfFiniteType u] [QuasiCompact u]
    (hdense : Dense ((O₁ ⊓ O₂ : U.Opens) : Set U)) :
    IsDominant ((O₁ ⊓ O₂ : U.Opens).ι ≫ cm.j) := by
  have : IsNoetherian P.side₁.intermediate := P.side₁.isNoetherian_intermediate
  have : IsNoetherian P.side₂.intermediate := P.side₂.isNoetherian_intermediate
  have hj := cm.dense_range_j P.side₁.dense_range_intermediateU
    P.side₂.dense_range_intermediateU
  constructor
  rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  refine DenseRange.comp hj ?_ cm.j.continuous
  rw [DenseRange, Scheme.Opens.range_ι]
  exact hdense

/-- **Valuative lifting for the two-open candidate** (blueprint:
`proposition-compactifying-union-two-opens--1`): every valuative square for `W ⟶ S` whose
generic point factors through `O₁ ∩ O₂` has a unique lift. Extend the generic point to
the two proper ambient models, pass to a side whose extension avoids its forbidden
boundary (`TwoOpenSide.KeyDisjoint.avoids`), lift to the intermediate scheme of that
side and then along its proper admissible blow-up; uniqueness holds because `W ⟶ S` is
separated. -/
theorem valuativeCriterion_relativeTo :
    ValuativeCriterion.RelativeTo cm.w ((O₁ ⊓ O₂ : U.Opens).ι ≫ cm.j) := by
  refine ValuativeCriterion.RelativeTo.of_existsUnique ?_
  rintro ⟨R, K, i₁, i₂, ⟨wsq⟩⟩ ηU hηU
  let : Field (CommRingCat.of K) := ‹_›
  replace hηU : ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ cm.j = i₁ := hηU
  -- extend the generic point to the two proper ambient models
  have hexist : ∀ {O : U.Opens} (σ : TwoOpenSide u O) (hle : O₁ ⊓ O₂ ≤ O),
      ∃ g : Spec (CommRingCat.of R) ⟶ σ.X,
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g =
          ηU ≫ U.homOfLE hle ≫ σ.embX ∧ g ≫ σ.s = i₂ := by
    intro O σ hle
    have hcomm : (ηU ≫ U.homOfLE hle ≫ σ.embX) ≫ σ.s =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
      simp only [Category.assoc, TwoOpenSide.embX_s, Scheme.homOfLE_ι_assoc]
      rw [show ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ u =
        (ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ cm.j) ≫ cm.w by simp, hηU, wsq]
    have hE : ValuativeCriterion.Existence σ.s := by
      have huc' : (ValuativeCriterion.Existence ⊓ @QuasiCompact) σ.s := by
        rw [← UniversallyClosed.eq_valuativeCriterion]
        infer_instance
      exact huc'.1
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE
      { R := R
        K := K
        i₁ := ηU ≫ U.homOfLE hle ≫ σ.embX
        i₂ := i₂
        commSq := ⟨hcomm⟩ }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  obtain ⟨g₁, hg₁, hg₁s⟩ := hexist P.side₁ inf_le_left
  obtain ⟨g₂, hg₂, hg₂s⟩ := hexist P.side₂ inf_le_right
  -- the avoiding extension lifts to the glued scheme through the corresponding
  -- intermediate scheme and its proper admissible blow-up
  have branch : ∀ {O : U.Opens} (σ : TwoOpenSide u O) (hle : O₁ ⊓ O₂ ≤ O)
      (B : IsAdmissible σ.intermediate σ.intermediateU.opensRange)
      (k : B.I.blowup ⟶ cm.W) (uu : U ⟶ B.I.blowup),
      uu ≫ B.I.blowupMap = σ.intermediateU →
      k ≫ cm.w = B.I.blowupMap ≫ σ.intermediateHom → uu ≫ k = cm.j →
      ∀ g : Spec (CommRingCat.of R) ⟶ σ.X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g = ηU ≫ U.homOfLE hle ≫ σ.embX →
      g ≫ σ.s = i₂ → (hrange : Set.range g ⊆ (σ.interior : Set σ.X)) →
      ∃ l : Spec (CommRingCat.of R) ⟶ cm.W,
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ cm.w = i₂ := by
    intro O σ hle B k uu huu hkw hglue g hg hgs hrange
    have hsqB : (ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ uu) ≫ B.I.blowupMap =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ.intermediateLift g hrange := by
      rw [σ.comp_intermediateLift g hrange _ (ηU ≫ U.homOfLE hle) (by rw [hg, Category.assoc])]
      simp only [Category.assoc, huu, Scheme.homOfLE_ι_assoc]
    have := B.isProper_blowupMap
    have hEB : ValuativeCriterion.Existence B.I.blowupMap := by
      have huc' : (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.I.blowupMap := by
        rw [← UniversallyClosed.eq_valuativeCriterion]
        infer_instance
      exact huc'.1
    obtain ⟨⟨n, hn₁, hn₂⟩⟩ := (hEB
      { R := R
        K := K
        i₁ := ηU ≫ (O₁ ⊓ O₂ : U.Opens).ι ≫ uu
        i₂ := σ.intermediateLift g hrange
        commSq := ⟨hsqB⟩ }).exists_lift
    refine ⟨n ≫ k, ?_, ?_⟩
    · rw [← Category.assoc, hn₁]
      simp only [Category.assoc]
      rw [hglue, hηU]
    · rw [Category.assoc, hkw, ← Category.assoc, hn₂, σ.intermediateLift_hom, hgs]
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Spec (CommRingCat.of R) ⟶ cm.W,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ cm.w = i₂ := by
    obtain h₁ | h₂ := P.keyDisjoint.avoids ηU g₁ g₂ hg₁ hg₂ (by rw [hg₁s, hg₂s])
    · exact branch P.side₁ inf_le_left cm.B₁ cm.k₁ cm.u₁ cm.u₁_blowupMap cm.k₁_w
        cm.u₁_k₁ g₁ hg₁ hg₁s h₁
    · exact branch P.side₂ inf_le_right cm.B₂ cm.k₂ cm.u₂ cm.u₂_blowupMap cm.k₂_w
        cm.u₂_k₂ g₂ hg₂ hg₂s h₂
  -- uniqueness from separatedness of the glued scheme
  refine ⟨l, ⟨hl₁, hl₂⟩, fun l' hl' ↦ ?_⟩
  have huniq := IsSeparated.valuativeCriterion (f := cm.w)
    { R := R
      K := K
      i₁ := i₁
      i₂ := i₂
      commSq := ⟨wsq⟩ }
  exact congrArg CommSq.LiftStruct.l
    (@Subsingleton.elim _ huniq ⟨l', hl'.1, hl'.2⟩ ⟨l, hl₁, hl₂⟩)

/-- **Properness of the two-open candidate** (blueprint:
`proposition-compactifying-union-two-opens--1`): `W ⟶ S` is separated and of finite type, and
universally closed by the dense-source valuative criterion (Stacks Project Tag 0894)
applied to the dominant quasi-compact map `O₁ ∩ O₂ ⟶ W`. -/
theorem isProper_w [IsNoetherian S] [LocallyOfFiniteType u] [QuasiCompact u]
    (hdense : Dense ((O₁ ⊓ O₂ : U.Opens) : Set U)) : IsProper cm.w := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : IsNoetherian U := ⟨⟩
  have : CompactSpace (O₁ ⊓ O₂ : U.Opens).toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian (O₁ ⊓ O₂ : U.Opens).toScheme := ⟨⟩
  have := cm.isDominant hdense
  have : UniversallyClosed cm.w :=
    UniversallyClosed.of_valuativeCriterion_of_isDominant cm.w _
      cm.valuativeCriterion_relativeTo
  exact ⟨⟩

/-- **The two-open compactification** (blueprint: `proposition-compactifying-union-two-opens--1`):
the open immersion `U ⟶ W` into the final common modification, which is proper over `S`. -/
def compactification [IsNoetherian S] [LocallyOfFiniteType u] [QuasiCompact u]
    (hdense : Dense ((O₁ ⊓ O₂ : U.Opens) : Set U)) : Compactification u where
  Z := cm.W
  g := cm.w
  i := cm.j
  comm := cm.j_comp_w.symm
  isProper := cm.isProper_w hdense
  isOpenImmersion := inferInstance

end FinalModification

end TwoOpenPreparation

/-- **The two-open compactification theorem** (Stacks Project Tag 0F40; blueprint:
`proposition-compactifying-union-two-opens`, `proposition-compactifying-union-two-opens--1`; proof
order items 43–48).

The compactification is the final common modification `W` (Stacks Project Tag 0F3X) of
the two intermediate schemes `Wᵢ = U ⊔_{Oᵢ} Xᵢ°`
(`TwoOpenPreparation.FinalModification.compactification`). -/
theorem HasCompactification.of_two_open_cover [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens)
    (hcov : O₁ ⊔ O₂ = ⊤) (hdense : Dense ((O₁ ⊓ O₂ : U.Opens) : Set U))
    [HasCompactification (O₁.ι ≫ u)] [HasCompactification (O₂.ι ≫ u)] :
    HasCompactification u := by
  obtain ⟨P⟩ := nonempty_twoOpenPreparation u O₁ O₂ hcov
  exact ⟨⟨P.finalModification.compactification hdense⟩⟩

end AlgebraicGeometry
