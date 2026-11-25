/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Gluing

/-! # Gluing closed loci representing a local predicate

Source: Stacks Project, Tag 0BDL, gluing of local closed subschemes.
(blueprint: lem-sc-local-closed-locus-gluing).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Closed representatives of a predicate stable under open restriction and local
on the source glue over an open cover of the target.
Source: Stacks Project, Tag 0BDL, final gluing paragraph; Schemes, Tags 01JB and 01JC.
(blueprint: lem-sc-local-closed-locus-gluing).

Proof: Choose the given neighbourhood at each target point. On an overlap,
pull back the two closed representatives. Their maps into every scheme over
the overlap satisfy the same predicate, so they represent the same subfunctor
of the functor of points of the overlap. Closed immersions are monomorphisms,
so Yoneda gives unique comparison isomorphisms over the overlap. Uniqueness
gives the cocycle condition. Glue the schemes along these open overlaps and
glue their structure maps to X. Closed immersion and local finite presentation
are local on the target, so the glued map has both properties. A map through
the glued scheme locally factors through the chart representatives, hence
satisfies P by source locality. Conversely restrict a map satisfying P to the
inverse images of the chosen target opens. Restriction stability gives P on
each such source open; the chart criteria supply local lifts, unique because
the chart maps are monomorphisms. The lifts agree on overlaps and glue.
For an empty target use the empty closed subscheme. Source locality forces P
on the empty source, as required. Neither quasi-compactness of X nor a finite
cover is assumed. -/
theorem exists_closedLocus_of_local_charts
    (X : Scheme.{u}) (P : ∀ T : Scheme.{u}, (T ⟶ X) → Prop)
    (hrestrict : ∀ (T : Scheme.{u}) (h : T ⟶ X) (V : T.Opens),
      P T h → P V.toScheme (V.ι ≫ h))
    (hlocal : ∀ (T : Scheme.{u}) (h : T ⟶ X),
      (∀ x : T, ∃ V : T.Opens, x ∈ V ∧ P V.toScheme (V.ι ≫ h)) → P T h)
    (hcharts : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ V.toScheme),
        IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
        (∀ (T : Scheme.{u}) (h : T ⟶ V.toScheme),
          (∃ g : T ⟶ Z, g ≫ i = h) ↔ P T (h ≫ V.ι))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ X),
        (∃ g : T ⟶ Z, g ≫ i = h) ↔ P T h) := by
  classical
  choose U hx Z i hi hfp hfactor using hcharts
  have (x : X) : IsClosedImmersion (i x) := hi x
  have (x : X) : LocallyOfFinitePresentation (i x) := hfp x
  let F (x : X) : Z x ⟶ X := i x ≫ (U x).ι
  have (x : X) : Mono (F x) := inferInstanceAs (Mono (i x ≫ (U x).ι))
  let V (x y : X) : (Z x).Opens := F x ⁻¹ᵁ U y
  have hself (x : X) : V x x = ⊤ := by
    simp only [V, F, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hP (x : X) : P (Z x) (F x) :=
    (hfactor x (Z x) (i x)).mp ⟨𝟙 _, by simp⟩
  have hlift (x y : X) : ∃ g : (V x y).toScheme ⟶ Z y,
      g ≫ F y = (V x y).ι ≫ F x := by
    obtain ⟨g, hg⟩ := (hfactor y _ (F x ∣_ U y)).mpr
      (by simpa only [morphismRestrict_ι] using hrestrict _ (F x) (V x y) (hP x))
    exact ⟨g, by
      dsimp only [F]
      rw [← Category.assoc, hg, morphismRestrict_ι]⟩
  choose g hg using hlift
  have hrange (x y : X) : Set.range (g x y) ⊆ Set.range (V y x).ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨g x y z, ?_⟩, rfl⟩
    change F y (g x y z) ∈ U x
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
    exact ((i x) ((V x y).ι z)).property
  let t (x y : X) : (V x y).toScheme ⟶ (V y x).toScheme :=
    IsOpenImmersion.lift (V y x).ι (g x y) (hrange x y)
  have ht (x y : X) : t x y ≫ (V y x).ι ≫ F y = (V x y).ι ≫ F x := by
    dsimp only [t]
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hg]
  let L (x y z : X) : pullback (V x y).ι (V x z).ι ⟶ (V y z).toScheme :=
    IsOpenImmersion.lift (V y z).ι
      (pullback.fst _ _ ≫ t x y ≫ (V y x).ι) (by
        rintro _ ⟨p, rfl⟩
        refine ⟨⟨(pullback.fst _ _ ≫ t x y ≫ (V y x).ι) p, ?_⟩, rfl⟩
        change F y ((pullback.fst _ _ ≫ t x y ≫ (V y x).ι) p) ∈ U z
        rw [← Scheme.Hom.comp_apply]
        simp only [Category.assoc, ht]
        rw [← Category.assoc, pullback.condition, Scheme.Hom.comp_apply]
        exact (pullback.snd (V x y).ι (V x z).ι p).property)
  have hL (x y z : X) : L x y z ≫ (V y z).ι =
      pullback.fst _ _ ≫ t x y ≫ (V y x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let tp (x y z : X) : pullback (V x y).ι (V x z).ι ⟶
      pullback (V y z).ι (V y x).ι :=
    pullback.lift (L x y z) (pullback.fst _ _ ≫ t x y) (hL x y z)
  have htp2 (x y z : X) : tp x y z ≫ pullback.snd _ _ ≫ (V y x).ι ≫ F y =
      pullback.snd _ _ ≫ (V x z).ι ≫ F x := by
    dsimp only [tp]
    rw [pullback.lift_snd_assoc]
    simp only [Category.assoc, ht]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  let D : Scheme.GlueData :=
    { J := X
      U := Z
      V := fun p ↦ (V p.1 p.2).toScheme
      f := fun x y ↦ (V x y).ι
      f_id := fun x ↦ by rw [hself]; exact inferInstanceAs (IsIso (Z x).topIso.hom)
      t := t
      t_id := fun x ↦ by
        apply (cancel_mono ((V x x).ι ≫ F x)).mp
        simpa only [Category.assoc, Category.id_comp] using ht x x
      t' := tp
      t_fac := fun _ _ _ ↦ pullback.lift_snd _ _ _
      cocycle := fun x y z ↦ by
        apply (cancel_mono (pullback.snd (V x y).ι (V x z).ι ≫
          (V x z).ι ≫ F x)).mp
        simp only [Category.assoc, htp2, Category.id_comp]
      f_open := fun _ _ ↦ inferInstance }
  let : HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  let q : D.glued ⟶ X := Multicoequalizer.desc D.toGlueData.diagram X F (by
    rintro ⟨x, y⟩
    exact (ht x y).symm)
  have hq (x : X) : D.ι x ≫ q = F x := by
    exact Multicoequalizer.π_desc D.toGlueData.diagram X _ _ x
  have (x : X) : IsOpenImmersion (D.ι x) := D.ι_isOpenImmersion x
  have hpreimage (x : X) : q ⁻¹ᵁ U x = (D.ι x).opensRange := by
    apply TopologicalSpace.Opens.ext
    ext z
    constructor
    · intro hz
      obtain ⟨y, zy, rfl⟩ := D.ι_jointly_surjective z
      have hy : zy ∈ V y x := by
        change F y zy ∈ U x
        change q (D.ι y zy) ∈ U x at hz
        rw [← Scheme.Hom.comp_apply, hq] at hz
        exact hz
      refine ⟨(t y x ≫ (V x y).ι) ⟨zy, hy⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      have heq := congrArg
        (fun k : (V y x).toScheme ⟶ D.glued ↦ k ⟨zy, hy⟩)
        (D.glue_condition y x)
      exact heq
    · rintro ⟨zy, rfl⟩
      change q (D.ι x zy) ∈ U x
      rw [← Scheme.Hom.comp_apply, hq]
      exact (i x zy).property
  have hpb (x : X) : IsPullback (i x) (D.ι x) (U x).ι q :=
    IsOpenImmersion.isPullback (i x) (D.ι x) (U x).ι q (hq x)
      (by simpa only [Scheme.Opens.opensRange_ι] using hpreimage x)
  have hcover : ⨆ x, U x = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let C : X.OpenCover := X.openCoverOfIsOpenCover U hcover
  have hclosed : IsClosedImmersion q := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
    intro x
    have H : IsClosedImmersion ((hpb x).flip.isoPullback.inv ≫ i x) := inferInstance
    rwa [(hpb x).flip.isoPullback_inv_snd] at H
  have hfinite : LocallyOfFinitePresentation q := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) C
    intro x
    have H : LocallyOfFinitePresentation ((hpb x).flip.isoPullback.inv ≫ i x) :=
      inferInstance
    rwa [(hpb x).flip.isoPullback_inv_snd] at H
  have : IsClosedImmersion q := hclosed
  refine ⟨D.glued, q, hclosed, hfinite, ?_⟩
  intro T h
  constructor
  · rintro ⟨g, rfl⟩
    apply hlocal
    intro y
    obtain ⟨x, z, hz⟩ := D.ι_jointly_surjective (g y)
    let W : T.Opens := g ⁻¹ᵁ (D.ι x).opensRange
    have hW : y ∈ W := ⟨z, hz⟩
    have hr : Set.range (W.ι ≫ g) ⊆ Set.range (D.ι x) := by
      rintro _ ⟨w, rfl⟩
      change g w.val ∈ Set.range (D.ι x)
      exact w.property
    let d : W.toScheme ⟶ Z x := IsOpenImmersion.lift (D.ι x) (W.ι ≫ g) hr
    have hd : d ≫ D.ι x = W.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
    have hfree := (hfactor x W.toScheme (d ≫ i x)).mp ⟨d, rfl⟩
    refine ⟨W, hW, ?_⟩
    have heq : (d ≫ i x) ≫ (U x).ι = W.ι ≫ g ≫ q := by
      change d ≫ F x = _
      rw [← hq, ← Category.assoc, hd, Category.assoc]
    exact heq ▸ hfree
  · intro hfree
    let W (x : X) : T.Opens := h ⁻¹ᵁ U x
    have hW : ⨆ x, W x = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨h y, hx (h y)⟩
    let CT : T.OpenCover := T.openCoverOfIsOpenCover W hW
    have hlifts (x : X) : ∃ g : (W x).toScheme ⟶ D.glued,
        g ≫ q = (W x).ι ≫ h := by
      obtain ⟨k, hk⟩ := (hfactor x _ (h ∣_ U x)).mpr
        (by simpa only [morphismRestrict_ι] using hrestrict T h (W x) hfree)
      refine ⟨k ≫ D.ι x, ?_⟩
      rw [Category.assoc, hq]
      dsimp only [F]
      rw [← Category.assoc, hk, morphismRestrict_ι]
    choose k hk using hlifts
    have hcompat (x y : X) : pullback.fst (CT.f x) (CT.f y) ≫ k x =
        pullback.snd _ _ ≫ k y := by
      apply (cancel_mono q).mp
      simp only [Category.assoc, hk]
      exact pullback.condition_assoc h
    refine ⟨CT.glueMorphisms k hcompat, ?_⟩
    apply CT.hom_ext
    intro x
    rw [CT.ι_glueMorphisms_assoc]
    exact hk x

end AlgebraicGeometry.Scheme
