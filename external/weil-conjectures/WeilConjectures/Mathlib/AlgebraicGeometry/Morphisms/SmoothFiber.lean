/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Smoothness by flatness and smooth fibres

A morphism of schemes is smooth if and only if it is flat, locally of finite presentation, and
all its fibres are smooth over the residue fields.

## Main statements

- `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`:
  the fibrewise criterion for smoothness.
- `AlgebraicGeometry.smooth_iff_flat_and_smooth_fiber`: the same criterion for `f` locally of
  finite presentation.
- `AlgebraicGeometry.Scheme.Hom.fiberι_mem_smoothLocus`: the pointwise fibrewise criterion: a
  flat morphism, locally of finite presentation, is smooth at every point at which its fibre is
  smooth.

## References

- Stacks Project, Lemma 29.35.3, <https://stacks.math.columbia.edu/tag/01V8>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **A smooth morphism is flat and locally of finite presentation.** Both are Mathlib instances
for `Smooth f`.

(blueprint: `lem-pc-smooth-flat`) -/
theorem Smooth.flat_and_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    Flat f ∧ LocallyOfFinitePresentation f :=
  ⟨inferInstance, inferInstance⟩


/-- **Smoothness by flatness and smooth fibres** (blueprint `lem-pc-smooth-characterization`). A
morphism `f : X ⟶ Y` is smooth if and only if it is flat, locally of finite presentation, and
every fibre `X_y ⟶ Spec κ(y)` is smooth. A smooth morphism is flat and locally of finite
presentation, and its fibres are smooth by base change; the converse is
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`.

This is also blueprint `lem-pc-smooth-characterization`, stated there for `f` locally of finite
presentation. -/
@[stacks 01V8]
theorem smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Smooth f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧
      ∀ y, Smooth (f.fiberToSpecResidueField y) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, fun _ ↦
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))⟩,
    fun ⟨_, _, h⟩ ↦ .of_smooth_fiberToSpecResidueField f h⟩

/-- **Smoothness versus flatness.** A morphism `f : X ⟶ Y` locally of finite presentation is
smooth if and only if it is flat and every fibre `X_y ⟶ Spec κ(y)` is smooth.

(blueprint: `lem-pc-smooth-characterization`) -/
@[stacks 01V8]
theorem smooth_iff_flat_and_smooth_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] :
    Smooth f ↔ Flat f ∧ ∀ y, Smooth (f.fiberToSpecResidueField y) := by
  rw [smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField]
  exact ⟨fun ⟨h₁, _, h₃⟩ ↦ ⟨h₁, h₃⟩, fun ⟨h₁, h₃⟩ ↦ ⟨h₁, ‹_›, h₃⟩⟩

/-- The fibres of a morphism locally of finite presentation are locally of finite
presentation. -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (y : Y) :
    LocallyOfFinitePresentation (f.fiberToSpecResidueField y) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

/-- Postcomposing with an open immersion does not change the smooth locus: the stalk maps differ
by an isomorphism. -/
lemma Scheme.Hom.smoothLocus_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (j : Y ⟶ Z) [IsOpenImmersion j] [LocallyOfFinitePresentation g] :
    (g ≫ j).smoothLocus = g.smoothLocus := by
  ext x
  refine Iff.trans ?_ (RingHom.FormallySmooth.respectsIso.cancel_left_isIso (j.stalkMap (g x))
    (g.stalkMap x))
  rw [← CommRingCat.hom_comp, ← stalkMap_comp]
  rfl

/-- Let `g ≫ j = i ≫ f` with `i` and `j` open immersions. If the fibre of `g` over `z` maps into
the smooth locus of the fibre of `f` over `j z`, then the fibre of `g` over `z` is smooth: it is
an open subscheme of the fibre of `f` over `j z`, compatibly with `κ(z) ≅ κ(j z)`. -/
lemma smooth_fiberToSpecResidueField_of_comp_eq {X' Y' X Y : Scheme.{u}} (g : X' ⟶ Y')
    (i : X' ⟶ X) (f : X ⟶ Y) (j : Y' ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (w : g ≫ j = i ≫ f) (z : Y')
    (h : ∀ v : g.fiber z, ∃ v' ∈ (f.fiberToSpecResidueField (j z)).smoothLocus,
      f.fiberι (j z) v' = i (g.fiberι z v)) :
    Smooth (g.fiberToSpecResidueField z) := by
  let N : g.fiber z ⟶ f.fiber (j z) := pullback.map _ _ _ _ i (Spec.map (j.residueFieldMap z)) j
    w (by simp)
  have : IsOpenImmersion N := Scheme.pullback_map_isOpenImmersion ..
  have hN₁ : N ≫ f.fiberι (j z) = g.fiberι z ≫ i := pullback.lift_fst _ _ _
  have hN₂ : (g.fiberToSpecResidueField z).smoothLocus =
      N ⁻¹ᵁ (f.fiberToSpecResidueField (j z)).smoothLocus := by
    rw [← Scheme.Hom.smoothLocus_comp_of_isOpenImmersion _ (Spec.map (j.residueFieldMap z)),
      Scheme.Hom.preimage_smoothLocus_eq]
    congr 1
    exact (pullback.lift_snd _ _ _).symm
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, hN₂, eq_top_iff]
  rintro v -
  obtain ⟨v', hv', hv'v⟩ := h v
  rwa [Scheme.Hom.mem_preimage, ← (f.fiberι (j z)).isEmbedding.injective
    (hv'v.trans (by rw [← Scheme.Hom.comp_apply, ← hN₁, Scheme.Hom.comp_apply]) :
      f.fiberι (j z) v' = f.fiberι (j z) (N v))]

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise fibrewise criterion for `Spec S ⟶ Spec R`: if `Spec S ⟶ Spec R` is flat, of
finite presentation and its fibre over the image of `x` is smooth, then it is smooth at `x`
(`Algebra.IsSmoothAt.of_formallySmooth_fiber`). -/
lemma mem_smoothLocus_SpecMap_of_smooth_fiberToSpecResidueField {R S : CommRingCat.{u}}
    (φ : R ⟶ S) [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)] (x : Spec S)
    (h : Smooth ((Spec.map φ).fiberToSpecResidueField (Spec.map φ x))) :
    x ∈ (Spec.map φ).smoothLocus := by
  have hfl : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have hfp : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp ‹_›
  algebraize [φ.hom]
  let p : PrimeSpectrum R := Spec.map φ x
  have : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  let q : PrimeSpectrum S := x
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hq : Algebra.IsSmoothAt R q.asIdeal := .of_formallySmooth_fiber p.asIdeal q.asIdeal
  rw [Scheme.Hom.mem_smoothLocus, RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso φ x)]
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have : Algebra.FormallySmooth (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := Algebra.FormallySmooth.iff_restrictScalars (R := R).mp hq
  exact RingHom.formallySmooth_algebraMap.mpr this

set_option backward.isDefEq.respectTransparency false in
/-- **Pointwise fibrewise criterion for smoothness**. Let `f : X ⟶ Y` be flat and locally of
finite presentation. If the fibre `X_y ⟶ Spec κ(y)` is smooth at `w`, then `f` is smooth at the
image of `w` in `X`. We shrink to affine opens `V ⊆ f ⁻¹ U` whose fibre over `y` lies in the
smooth locus of the fibre and apply
`AlgebraicGeometry.mem_smoothLocus_SpecMap_of_smooth_fiberToSpecResidueField`. -/
theorem Scheme.Hom.fiberι_mem_smoothLocus {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] {y : Y} {w : f.fiber y}
    (hw : w ∈ (f.fiberToSpecResidueField y).smoothLocus) : f.fiberι y w ∈ f.smoothLocus := by
  obtain ⟨G, hG, hGw⟩ := (f.fiberι y).isEmbedding.isInducing.isOpen_iff.mp
    (f.fiberToSpecResidueField y).smoothLocus.2
  have hfx : f (f.fiberι y w) = y := (f.range_fiberι y).subset ⟨w, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxG : f.fiberι y w ∈ G := by
    rw [← Set.mem_preimage, hGw]
    exact hw
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVUG⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := f.fiberι y w) (u := (f ⁻¹ᵁ U : Set X) ∩ G) ⟨by rwa [SetLike.mem_coe,
      Scheme.Hom.mem_preimage, hfx], hxG⟩ ((f ⁻¹ᵁ U).2.inter hG)
  have hVU : V ≤ f ⁻¹ᵁ U := fun v hv ↦ (hVUG hv).1
  obtain ⟨x', hx'⟩ : f.fiberι y w ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hxV
  have hw' := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU
  have : Flat (Spec.map (f.appLE U V hVU)) :=
    HasRingHomProperty.Spec_iff.mpr (f.flat_appLE hU hV hVU)
  have : LocallyOfFinitePresentation (Spec.map (f.appLE U V hVU)) :=
    HasRingHomProperty.Spec_iff.mpr (f.finitePresentation_appLE hU hV hVU)
  have hz : hU.fromSpec (Spec.map (f.appLE U V hVU) x') = y := by
    rw [← Scheme.Hom.comp_apply, hw', Scheme.Hom.comp_apply, hx', hfx]
  subst hz
  have hsm := mem_smoothLocus_SpecMap_of_smooth_fiberToSpecResidueField _ x'
    (smooth_fiberToSpecResidueField_of_comp_eq _ hV.fromSpec f hU.fromSpec hw' _ fun v ↦ ?_)
  · have e : (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec).smoothLocus =
        hV.fromSpec ⁻¹ᵁ f.smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_eq]
      congr 1
    rwa [← Scheme.Hom.smoothLocus_comp_of_isOpenImmersion _ hU.fromSpec, e,
      Scheme.Hom.mem_preimage, hx'] at hsm
  · have hpV : hV.fromSpec ((Spec.map (f.appLE U V hVU)).fiberι _ v) ∈ V :=
      hV.range_fromSpec.subset ⟨_, rfl⟩
    have hfp : f (hV.fromSpec ((Spec.map (f.appLE U V hVU)).fiberι _ v)) =
        hU.fromSpec (Spec.map (f.appLE U V hVU) x') := by
      rw [← Scheme.Hom.comp_apply, ← hw', Scheme.Hom.comp_apply,
        ((Spec.map (f.appLE U V hVU)).range_fiberι _).subset ⟨v, rfl⟩]
    obtain ⟨v', hv'⟩ := (f.range_fiberι _).symm.subset hfp
    refine ⟨v', ?_, hv'⟩
    refine (Set.ext_iff.mp hGw v').mp ?_
    rw [Set.mem_preimage, hv']
    exact (hVUG hpV).2

end AlgebraicGeometry
