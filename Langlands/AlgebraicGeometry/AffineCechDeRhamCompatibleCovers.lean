import Langlands.AlgebraicGeometry.AffineCechDeRhamInfinitesimalMorphism
import Langlands.AlgebraicGeometry.AffineCechFunctionBaseChange

/-! # Finite affine refinements compatible with a reduced morphism -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (hI : I * I = ⊥)
  (m : quotientReduction f I ⟶ Y)
  (U : Scheme.AffineOpenCover.{u} X) (V : Scheme.AffineOpenCover.{u} Y)

local notation "q" => quotientReductionMap f I

/-- A finite source cover refining a given affine cover and compatible with
the reduced morphism into a prescribed target cover. -/
structure ReducedChartRefinement where
  cover : Scheme.AffineOpenCover.{u} X
  [finite : Finite cover.I₀]
  sourceIndex : cover.I₀ → U.I₀
  sourceLE : ∀ i, coverOpens cover i ≤ coverOpens U (sourceIndex i)
  targetIndex : cover.I₀ → V.I₀
  targetLE : ∀ i, q ⁻¹ᵁ coverOpens cover i ≤ m ⁻¹ᵁ coverOpens V (targetIndex i)

attribute [instance] ReducedChartRefinement.finite

include hI in
theorem nonempty_reducedChartRefinement [CompactSpace X] :
    Nonempty (ReducedChartRefinement f I m U V) := by
  classical
  let : Surjective q := quotientReductionMap_surjective f I hI
  let e : quotientReduction f I ≃ₜ X :=
    (q).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective (q).surjective
  let δ (x : X) : V.I₀ := V.idx (m (e.symm x))
  let O (j : V.I₀) : X.Opens :=
    ⟨e.symm ⁻¹' (m ⁻¹ᵁ coverOpens V j : Set (quotientReduction f I)),
      (m ⁻¹ᵁ coverOpens V j).isOpen.preimage e.symm.continuous⟩
  have hO (j : V.I₀) : q ⁻¹ᵁ O j = m ⁻¹ᵁ coverOpens V j := by
    ext y
    change e.symm (q y) ∈ (m ⁻¹ᵁ coverOpens V j) ↔ y ∈ (m ⁻¹ᵁ coverOpens V j)
    rw [show e.symm (q y) = y from e.symm_apply_apply y]
  have h (x : X) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      W ≤ coverOpens U (U.idx x) ⊓ O (δ x) := by
    have hx : x ∈ coverOpens U (U.idx x) ⊓ O (δ x) :=
      ⟨U.covers x, V.covers (m (e.symm x))⟩
    obtain ⟨W, hW, hxW, hle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact ⟨W, hW, hxW, hle⟩
  choose W hW hxW hle using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  have hc : (⨆ i : t, W i.1) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  let C := affineCoverOfOpens (fun i : t => W i.1) (fun i => hW i.1) hc
  refine ⟨{ cover := C
            finite := inferInstanceAs (Finite ↑t)
            sourceIndex := fun i => U.idx i.1
            sourceLE := ?_
            targetIndex := fun i => δ i.1
            targetLE := ?_ }⟩
  · intro i
    rw [coverOpens_affineCoverOfOpens]
    exact (hle i.1).trans inf_le_left
  · intro i
    rw [coverOpens_affineCoverOfOpens, ← hO]
    exact (q).preimage_mono ((hle i.1).trans inf_le_right)

end Langlands.AlgebraicGeometry.AffineCechDeRham
