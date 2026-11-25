/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding

/-!
# Smooth morphisms are locally of constant relative dimension

A smooth morphism `f : X ⟶ Y` is, locally on the source, smooth of some relative dimension:

* `RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension`: a standard smooth ring
  homomorphism is standard smooth of some relative dimension;
* `AlgebraicGeometry.smoothOfRelativeDimension_ι_comp_of_appLE`: if `f.appLE U V e` is standard
  smooth of relative dimension `n` for affine opens `U` and `V`, the restriction `V ⟶ Y` of `f`
  is smooth of relative dimension `n`, and hence
  (`AlgebraicGeometry.Smooth.exists_mem_smoothOfRelativeDimension_ι_comp`) a smooth morphism is
  smooth of some relative dimension on a neighbourhood of every point;
* `AlgebraicGeometry.exists_finite_openCover_smoothOfRelativeDimension`: for a smooth morphism
  `f : X ⟶ Y` of schemes over a field with `X` quasi-compact, `X` is covered by finitely many opens
  on each of which `f` is smooth of some relative dimension;
* `AlgebraicGeometry.exists_finite_openCover_smoothOfRelativeDimension_of_isPullback`: the
  preimages of such a cover along a cartesian square over `f` cover the source of the base change
  `f'`, which is smooth of the same relative dimensions on them
  (`AlgebraicGeometry.smoothOfRelativeDimension_ι_comp_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory

/-- A standard smooth ring homomorphism is standard smooth of some relative dimension. -/
lemma RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension {R S : Type*}
    [CommRing R] [CommRing S] {f : R →+* S} (hf : f.IsStandardSmooth) :
    ∃ n : ℕ, f.IsStandardSmoothOfRelativeDimension n := by
  algebraize [f]
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
  exact ⟨P.dimension, ⟨ι, σ, ‹_›, ‹_›, P, rfl⟩⟩

namespace AlgebraicGeometry

/-- If `f.appLE U V e` is standard smooth of relative dimension `n` for affine opens `U` of `Y`
and `V` of `X`, then the restriction `V ⟶ Y` of `f` is smooth of relative dimension `n`. -/
lemma smoothOfRelativeDimension_ι_comp_of_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hf : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n),
      Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    have H := RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))
    rw [CommRingCat.hom_comp, H.cancel_left_isIso, CommRingCat.hom_comp, H.cancel_right_isIso]
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _ hf
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- A smooth morphism is smooth of some relative dimension on an open neighbourhood of every
point of the source. -/
lemma Smooth.exists_mem_smoothOfRelativeDimension_ι_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ := hf.exists_isStandardSmoothOfRelativeDimension
  exact ⟨V, hxV, n, smoothOfRelativeDimension_ι_comp_of_appLE f hU hV e hn⟩

/-- **Smooth morphisms are of locally constant relative dimension**: for a smooth morphism
`f : X ⟶ Y` of schemes over a field `k` with `X` quasi-compact over `k`, `X` is covered by finitely
many opens `U i` such that each restriction `U i ⟶ Y` of `f` is smooth of some relative
dimension. -/
theorem exists_finite_openCover_smoothOfRelativeDimension {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))} [QuasiCompact X.hom] (f : X ⟶ Y) [Smooth f.left] :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → X.left.Opens), (⨆ i, U i) = ⊤ ∧
      ∀ i, ∃ d : ℕ, SmoothOfRelativeDimension d (overRestrictι X (U i) ≫ f).left := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  choose V hxV n hn using Smooth.exists_mem_smoothOfRelativeDimension_ι_comp f.left
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X.left))
    (fun x ↦ (V x).isOpen) fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩
  refine ⟨Fin t.card, inferInstance, fun i ↦ V (t.equivFin.symm i), eq_top_iff.2 fun x _ ↦ ?_,
    fun i ↦ ⟨n _, hn _⟩⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

/-- Being smooth of relative dimension `d` on an open `U` is stable under base change: for a
cartesian square `X' ⟶ X`, `X' ⟶ Y'` over `f : X ⟶ Y`, `g : Y' ⟶ Y`, if the restriction
`U ⟶ Y` of `f` is smooth of relative dimension `d`, so is the restriction `g' ⁻¹ᵁ U ⟶ Y'`
of `f'`. -/
lemma smoothOfRelativeDimension_ι_comp_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (h : IsPullback g' f' f g) {d : ℕ} (U : X.Opens)
    [SmoothOfRelativeDimension d (U.ι ≫ f)] :
    SmoothOfRelativeDimension d ((g' ⁻¹ᵁ U).ι ≫ f') :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  MorphismProperty.of_isPullback ((isPullback_morphismRestrict g' U).paste_vert h) ‹_›

/-- **Smooth morphisms are of locally constant relative dimension, compatibly with base
change**: for a smooth morphism `f : X ⟶ Y` of schemes over a field `k` with `X` quasi-compact
over `k` and a cartesian square `X' ⟶ X`, `X' ⟶ Y'` over `f` and `g : Y' ⟶ Y`, there are
finitely many opens `U i` covering `X` such that each restriction `U i ⟶ Y` of `f` is smooth of
some relative dimension `d`, and then the preimages `g' ⁻¹ᵁ U i` cover `X'` and the restriction
`g' ⁻¹ᵁ U i ⟶ Y'` of `f'` is smooth of the same relative dimension `d`. -/
theorem exists_finite_openCover_smoothOfRelativeDimension_of_isPullback {k : Type u} [Field k]
    {X Y X' Y' : Over (Spec (.of k))} [QuasiCompact X.hom] (f : X ⟶ Y) [Smooth f.left]
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (h : IsPullback g'.left f'.left f.left g.left) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → X.left.Opens), (⨆ i, U i) = ⊤ ∧
      (⨆ i, g'.left ⁻¹ᵁ U i) = ⊤ ∧ ∀ i, ∃ d : ℕ,
        SmoothOfRelativeDimension d (overRestrictι X (U i) ≫ f).left ∧
        SmoothOfRelativeDimension d (overRestrictι X' (g'.left ⁻¹ᵁ U i) ≫ f').left := by
  obtain ⟨ι, hι, U, hU, hf⟩ := exists_finite_openCover_smoothOfRelativeDimension f
  refine ⟨ι, hι, U, hU, g'.left.iSup_preimage_eq_top hU, fun i ↦ ?_⟩
  obtain ⟨d, hd⟩ := hf i
  have : SmoothOfRelativeDimension d ((U i).ι ≫ f.left) := hd
  exact ⟨d, hd, smoothOfRelativeDimension_ι_comp_of_isPullback h (d := d) (U i)⟩

end AlgebraicGeometry
