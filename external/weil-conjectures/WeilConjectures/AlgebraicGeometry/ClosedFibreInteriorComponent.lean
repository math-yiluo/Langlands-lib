/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # ClosedFibreInteriorComponent

Source: Stacks Project, Tag 054X, second proof paragraph.
(blueprint: lem-sbc-closed-fibre-interior-component)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem local_dimension_le_of_embedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (j : A → B) (hj : IsEmbedding j) (a : A) :
    topologicalKrullDimAt a ≤ topologicalKrullDimAt (j a) := by
  unfold topologicalKrullDimAt
  refine le_iInf₂ fun W ha ↦ ?_
  let V : TopologicalSpace.Opens A := ⟨j ⁻¹' W, W.isOpen.preimage hj.continuous⟩
  refine (iInf₂_le V ha).trans ?_
  apply IsInducing.topologicalKrullDim_le (f := fun x : V ↦ (⟨j x, x.2⟩ : W))
  apply IsInducing.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
  exact hj.isInducing.comp IsInducing.subtypeVal

private theorem local_dimension_eq_of_embedding_interior {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (j : A → B) (hj : IsEmbedding j) (a : A)
    (ha : j a ∈ interior (Set.range j)) :
    topologicalKrullDimAt a = topologicalKrullDimAt (j a) := by
  refine le_antisymm (local_dimension_le_of_embedding j hj a) ?_
  unfold topologicalKrullDimAt
  refine le_iInf₂ fun V haV ↦ ?_
  obtain ⟨W, hW, hWV⟩ := hj.isInducing.isOpen_iff.mp V.isOpen
  let W' : TopologicalSpace.Opens B := ⟨W ∩ interior (Set.range j),
    hW.inter isOpen_interior⟩
  let V' : TopologicalSpace.Opens A := ⟨j ⁻¹' W', W'.isOpen.preimage hj.continuous⟩
  have haW : j a ∈ W' := ⟨by change a ∈ j ⁻¹' W; rw [hWV]; exact haV, ha⟩
  have hsub : (V' : Set A) ⊆ V := by
    intro x hx
    rw [← hWV]
    exact hx.1
  have hemb : IsEmbedding (fun x : V' ↦ j x) := hj.comp IsEmbedding.subtypeVal
  have hrange : Set.range (fun x : V' ↦ j x) = (W' : Set B) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨x, rfl⟩ := interior_subset hy.2
      exact ⟨⟨x, hy⟩, rfl⟩
  have heq : topologicalKrullDim V' = topologicalKrullDim W' := by
    rw [hemb.topologicalKrullDim_eq_range, hrange]
    rfl
  refine (iInf₂_le W' haW).trans (heq.symm.le.trans ?_)
  apply IsInducing.topologicalKrullDim_le (f := fun x : V' ↦ (⟨x, hsub x.2⟩ : V))
  apply IsInducing.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
  exact IsInducing.subtypeVal

private theorem component_of_embedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (j : A → B) (hj : IsClosedEmbedding j)
    (a : A) (ha : j a ∈ genericPoints B) : a ∈ genericPoints A := by
  refine ⟨isIrreducible_singleton.closure, fun V hV hsub ↦ ?_⟩
  have himage : IsIrreducible (j '' V) := hV.image j hj.continuous.continuousOn
  have hclosure : closure {j a} ⊆ j '' V := by
    rw [← Set.image_singleton, hj.closure_image_eq]
    exact Set.image_mono hsub
  have hle : j '' V ⊆ closure {j a} := ha.2 himage hclosure
  rw [hj.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  exact fun y hy ↦ hle ⟨y, hy, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- At an ambient fibre component point in the closed interior, the closed fibre
has the same local dimension and the point is generic in one of its components.
Source: Stacks Project, Tag 054X, second proof paragraph.
Proof: the closed immersion on fibres identifies the source fibre with the closed
inverse image of its range. The closure of the chosen ambient generic point is an
ambient component contained in that range. Its inverse image is an irreducible
component of the closed fibre, by maximality of the ambient component. The chosen
point is its generic point. On the open interior the closed immersion is a
homeomorphism onto an ambient open neighbourhood. Local dimension is unchanged
under a homeomorphism and under restriction to an open neighbourhood, so the two
local dimensions agree. This uses only topology, not flatness or finite type.
(blueprint: lem-sbc-closed-fibre-interior-component) -/
theorem common_fibre_component_dimension_of_mem_interior
    {Z X T : Scheme.{u}} (f : X ⟶ T) (i : Z ⟶ X) [IsClosedImmersion i]
    (z : Z)
    (hinterior : f.asFiber (i z) ∈
      interior ((f.fiberι (f (i z))) ⁻¹' Set.range i))
    (hcomponent : f.asFiber (i z) ∈ genericPoints (f.fiber (f (i z)))) :
    (i ≫ f).asFiber z ∈ genericPoints ((i ≫ f).fiber ((i ≫ f) z)) ∧
      topologicalKrullDimAt ((i ≫ f).asFiber z) =
        topologicalKrullDimAt (f.asFiber (i z)) := by
  let g := i ≫ f
  let t := f (i z)
  let j : g.fiber t ⟶ f.fiber t := CategoryTheory.Limits.pullback.map
    g (T.fromSpecResidueField t) f (T.fromSpecResidueField t)
    i (𝟙 _) (𝟙 _) (by simp [g]) (by simp)
  have hsq : IsPullback j (g.fiberι t) (f.fiberι t) i := by
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback f (T.fromSpecResidueField t)).flip
    · simpa [j, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, g] using
        (IsPullback.of_hasPullback g (T.fromSpecResidueField t)).flip
    · simp [j, Scheme.Hom.fiberι]
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hrange : Set.range j = (f.fiberι t) ⁻¹' Set.range i := by
    dsimp only [j, Scheme.Hom.fiber]
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Hom.fiberι]
  have hpoint : j (g.asFiber z) = f.asFiber (i z) := by
    apply (f.fiberι t).isEmbedding.injective
    change (j ≫ f.fiberι t) (g.asFiber z) = _
    rw [hsq.w, Scheme.Hom.comp_apply]
    change i ((g.fiberι (g z)) (g.asFiber z)) =
      (f.fiberι (f (i z))) (f.asFiber (i z))
    simp
  constructor
  · apply component_of_embedding j j.isClosedEmbedding (g.asFiber z)
    rwa [hpoint]
  · have hmem : j (g.asFiber z) ∈ interior (Set.range j) := by
      rwa [hpoint, hrange]
    exact (local_dimension_eq_of_embedding_interior j j.isEmbedding (g.asFiber z) hmem).trans
      (congrArg topologicalKrullDimAt hpoint)

end AlgebraicGeometry
