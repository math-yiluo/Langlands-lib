/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension
public import WeilConjectures.AlgebraicGeometry.GenericFiber.ProjectiveCoordinate

/-!
# Coordinate projections

Let `p : Y ⟶ S` be proper over an integral locally noetherian scheme, covered by finitely many
opens `Y_α` with closed immersions `e_α : Y_α ⟶ 𝔸^{σ_α}_S` over `S`, and write
`t_{α r} : Y_α ⟶ 𝔸¹_S` for the coordinate functions. This file bundles the two facts about the
`t_{α r}` used in Deligne's generic constructibility theorem:

1. the coordinates lower the dimension of the generic fibre of any open `X ⊆ Y` by one
   (`AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_add_one_le`);
2. over a nonempty open of `S`, the reduced complement of `⋃ t_{α r}⁻¹ V_{α r}` is finite, for
   dense opens `V_{α r} ⊆ 𝔸¹_S`
   (`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_range_subset`).

## Main statements

- `AlgebraicGeometry.coordinate_projections`

## Implementation details

The source takes `S` affine and noetherian and `p` projective; the statement here only needs `S`
integral and locally noetherian and `p` proper. The bound `dim ≤ n - 1` on the generic fibre is
stated as `dim + 1 ≤ n`, so that an empty fibre (of dimension `⊥`) is covered.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order Topology

namespace AlgebraicGeometry

/-- Restricting a morphism along an immersion does not increase the dimension of its fibres. -/
lemma topologicalKrullDim_fiber_comp_le {X X' S : Scheme.{u}} (g : X' ⟶ X) [IsPreimmersion g]
    (f : X ⟶ S) (s : S) :
    topologicalKrullDim ((g ≫ f).fiber s) ≤ topologicalKrullDim (f.fiber s) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((g ≫ f).fiberHomeo s).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph]
  refine IsInducing.topologicalKrullDim_le (f := Set.codRestrict (fun x ↦ g x.1) (f ⁻¹' {s})
    fun x ↦ by
      change f (g x.1) = s
      rw [← Scheme.Hom.comp_apply]
      exact x.2) ?_
  exact ((IsPreimmersion.isEmbedding g).isInducing.comp IsInducing.subtypeVal).codRestrict _

/-- Let `S` be an integral locally noetherian scheme with generic point `η`, let `p : Y ⟶ S` be
proper, let `Y = ⋃_α Y_α` be a finite open cover with closed immersions `e_α : Y_α ⟶ 𝔸^{σ_α}_S`
over `S`, and write `t_{α r} : Y_α ⟶ 𝔸¹_S` for the coordinate functions. Then:

1. if `X ⊆ Y` is open with `dim X_η ≤ n`, then for all `α, r` the generic fibre of
   `t_{α r} : X ∩ Y_α ⟶ 𝔸¹_S` has dimension at most `n - 1`;
2. if `V_{α r} ⊆ 𝔸¹_S` are dense opens and `G = ⋃_{α, r} t_{α r}⁻¹(V_{α r})`, then after
   shrinking `S` to a nonempty open `W`, the reduced closed complement `Z = Y \ G` is finite
   over `W`. -/
theorem coordinate_projections {S Y : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (p : Y ⟶ S) [IsProper p] {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ⨆ α, U α = ⊤)
    (σ : ι → Type u) [∀ α, Finite (σ α)] (e : ∀ α, (U α).toScheme ⟶ 𝔸(σ α; S))
    [∀ α, IsClosedImmersion (e α)] (he : ∀ α, e α ≫ 𝔸(σ α; S) ↘ S = (U α).ι ≫ p) :
    (∀ (X : Y.Opens) (n : ℕ), topologicalKrullDim ((X.ι ≫ p).fiber (genericPoint S)) ≤ n →
      ∀ α (r : σ α), topologicalKrullDim
        ((Y.homOfLE (inf_le_left : U α ⊓ X ≤ U α) ≫ e α ≫
          AffineSpace.reindex (fun _ : PUnit ↦ r) S).fiber (genericPoint 𝔸(PUnit; S))) + 1 ≤
        n) ∧
    ∀ (V : ∀ α, σ α → 𝔸(PUnit; S).Opens), (∀ α r, Dense (V α r : Set 𝔸(PUnit; S))) →
      let G : Y.Opens := ⨆ (α : ι) (r : σ α), (U α).ι ''ᵁ
        ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹ᵁ V α r)
      ∃ W : S.Opens, (W : Set S).Nonempty ∧
        IsFinite (((Scheme.IdealSheafData.vanishingIdeal G.compl).subschemeι ≫ p) ∣_ W) := by
  refine ⟨fun X n hX α r ↦ ?_, fun V hV ↦ ?_⟩
  · refine (topologicalKrullDim_fiber_genericPoint_add_one_le ((U α ⊓ X).ι ≫ p) _ ?_).trans ?_
    · simp [AffineSpace.reindex_over, he]
    · rw [← Y.homOfLE_ι (inf_le_right : U α ⊓ X ≤ X), Category.assoc]
      exact (topologicalKrullDim_fiber_comp_le _ _ _).trans hX
  · intro G
    have : Nonempty 𝔸(PUnit; S) := ⟨(𝔸(PUnit; S) ↘ S).surjective
      (Classical.arbitrary S) |>.choose⟩
    obtain ⟨W, hW, h⟩ := exists_isFinite_morphismRestrict_of_range_subset p U hU σ e he V
      fun α r ↦ (hV α r).nonempty
    refine ⟨W, hW, h _ _ ?_⟩
    have hG : Set.range (Scheme.IdealSheafData.vanishingIdeal G.compl).subschemeι =
        (G : Set Y)ᶜ := by
      simp [Scheme.IdealSheafData.range_subschemeι]
    rw [hG]
    refine Set.compl_subset_compl.mpr (Set.iUnion₂_subset fun α r ↦ ?_)
    exact SetLike.coe_mono (le_iSup₂ (f := fun (α : ι) (r : σ α) ↦ (U α).ι ''ᵁ
      ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹ᵁ V α r)) α r)

end AlgebraicGeometry
