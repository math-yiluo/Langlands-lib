/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNeighborhood
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Equalising morphisms out of a piece of a split neighbourhood

Let `f : X ⟶ Y` be finite, `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically closed
and `t` a geometric point of `X` over `y`. Two morphisms from the `t`-th piece of a split
neighbourhood `s` to a pointed étale neighbourhood `(V, v)` of `t`, both sending the point
`(u, t)` to `v`, agree after passing to a smaller split neighbourhood
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_pieceFunctor_map_comp_eq`): since `V` is étale
over `X`, the locus where the two morphisms agree is open in the piece
(`AlgebraicGeometry.FormallyUnramified.eqLocus`) and contains `(u, t)`; its complement is
closed in `U ×_Y X`, contains none of the points `(u, t')`, and is removed by the shrinking
lemma `AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot`.

This is one half of the initiality of the piece functor
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.pieceFunctor`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

namespace SplitNbhd

variable {f}

/-- The point `(u, t')` does not lie in the `t`-th piece for `t' ≠ t`. -/
lemma basePt_notMem_piece (s : SplitNbhd f y) {t t' : GeometricFiber f y} (h : t' ≠ t) :
    basePt f s.obj t' default ∉ s.piece t := by
  intro hmem
  have h₁ : basePt f s.obj t' default ∈ s.piece t' ⊓ s.piece t := ⟨s.mem t', hmem⟩
  rw [(s.disjoint t' t h).eq_bot] at h₁
  exact h₁

variable [IsFinite f] [IsAlgClosed Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Two morphisms out of a piece agreeing at the marked point agree after shrinking.** -/
theorem exists_pieceFunctor_map_comp_eq (t : GeometricFiber f y) (s : SplitNbhd f y)
    {d : (pointSmallEtale t.1).fiber.Elements} (g g' : (pieceFunctor t).obj s ⟶ d) :
    ∃ (s' : SplitNbhd f y) (k : s' ⟶ s),
      (pieceFunctor t).map k ≫ g = (pieceFunctor t).map k ≫ g' := by
  set V : X.Etale := d.1 with hV
  set a : (s.piece t).toScheme ⟶ V.left := g.val.left with ha
  set b : (s.piece t).toScheme ⟶ V.left := g'.val.left with hb
  have hab : a ≫ V.hom = b ≫ V.hom := by
    rw [ha, hb, MorphismProperty.Over.w, MorphismProperty.Over.w]
  -- the two morphisms agree at the point `(u, t)`
  have hv : (s.piecePt t).left ≫ a = (s.piecePt t).left ≫ b := by
    have h₁ : (s.piecePt t) ≫ (Etale.forget X).map g.val = d.2 := g.map_val
    have h₂ : (s.piecePt t) ≫ (Etale.forget X).map g'.val = d.2 := g'.map_val
    exact congrArg CategoryTheory.Over.Hom.left (h₁.trans h₂.symm)
  -- the open locus of the piece where they agree
  set E := FormallyUnramified.eqLocus V.hom a b hab with hE
  -- its complement in the piece, as a closed subset of `U ×_Y X` without any of the `(u, t')`
  set C : Set (pullback s.obj.1.hom f : Scheme.{u}) :=
    SetLike.coe (s.piece t) ∩ (Set.range (E.ι ≫ (s.piece t).ι).base)ᶜ with hC
  have hCc : IsClosed C := (s.isClopen t).isClosed.inter
    (E.ι ≫ (s.piece t).ι).isOpenEmbedding.isOpen_range.isClosed_compl
  have hnot : ∀ t', basePt f s.obj t' default ∉ C := by
    rintro t' ⟨h₁, h₂⟩
    by_cases htt : t' = t
    · subst htt
      apply h₂
      have hmem : (s.piecePt t').left (default : Spec (.of Ω)) ∈ (E : Set (s.piece t').toScheme) :=
        FormallyUnramified.range_subset_eqLocus V.hom a b hab _ hv ⟨(default : Spec (.of Ω)), rfl⟩
      rw [← Scheme.Opens.range_ι] at hmem
      obtain ⟨e, he⟩ := hmem
      refine ⟨e, ?_⟩
      rw [Scheme.Hom.comp_apply, he]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (congrArg (fun m ↦ m.base (default : Spec (.of Ω))) (piecePt_left_ι s t'))
    · exact s.basePt_notMem_piece htt h₁
  obtain ⟨c', k, hk⟩ := exists_hom_preimage_eq_bot f s.obj C hCc hnot
  refine ⟨s.pullbackDec k, s.pullbackDecHom k, ?_⟩
  apply Functor.Elements.hom_ext
  apply MorphismProperty.Over.Hom.ext
  change (pieceMap (s.pullbackDecHom k) t).left ≫ a = (pieceMap (s.pullbackDecHom k) t).left ≫ b
  -- the piece of the smaller neighbourhood maps into the agreement locus
  have hrange : Set.range (pieceMap (s.pullbackDecHom k) t).left.base ⊆ Set.range E.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hw
    have hx : (s.piece t).ι ((pieceMap (s.pullbackDecHom k) t).left w) ∈ C := by
      refine ⟨?_, ?_⟩
      · rw [← Scheme.Opens.range_ι]
        exact ⟨_, rfl⟩
      · rintro ⟨e, he⟩
        rw [Scheme.Hom.comp_apply] at he
        have he' := (s.piece t).ι.isOpenEmbedding.injective he
        apply hw
        rw [← he', ← Scheme.Opens.range_ι]
        exact Set.mem_range_self e
    have h₃ : ((pieceMap (s.pullbackDecHom k) t).left ≫ (s.piece t).ι) w =
        (((s.pullbackDec k).piece t).ι ≫ (f.Etale.map k.val).left) w := by
      rw [pieceMap_left_ι]
      rfl
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₃
    have : ((s.pullbackDec k).piece t).ι w ∈ (f.Etale.map k.val).left.base ⁻¹' C :=
      (congrArg (fun z ↦ z ∈ C) h₃).mp hx
    rw [hk] at this
    exact this
  have hfac := IsOpenImmersion.lift_fac E.ι (pieceMap (s.pullbackDecHom k) t).left hrange
  rw [← hfac, Category.assoc, Category.assoc, FormallyUnramified.eqLocus_ι_comp_eq]

end SplitNbhd

end AlgebraicGeometry.Scheme.Hom

end
