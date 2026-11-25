/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions

/-! # Transport of limit comparisons under canonical chart refinement

Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing).
(blueprint: lem-pc-overlap-comparison-refinement). -/

@[expose] public section

universe u v t u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Pseudofunctor.OverlapTransitions
open LocallyDiscreteOpToCat
variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S S' S'' : C} {X X' X'' : ι → C}
  {f : ∀ a, X a ⟶ S} {f' : ∀ a, X' a ⟶ S'} {f'' : ∀ a, X'' a ⟶ S''}
  {p : S' ⟶ S} {q : S'' ⟶ S'} {r : S'' ⟶ S}
  {p' : ∀ a, X' a ⟶ X a} {q' : ∀ a, X'' a ⟶ X' a} {r' : ∀ a, X'' a ⟶ X a}
  (w : ∀ a, p' a ≫ f a = f' a ≫ p)
  (w' : ∀ a, q' a ≫ f' a = f'' a ≫ q)
  (hr : q ≫ p = r) (hr' : ∀ a, q' a ≫ p' a = r' a)

set_option backward.isDefEq.respectTransparency false in
private lemma comp_comm (T : F.OverlapTransitions f)
    {Y : C} (s : Y ⟶ S'') {a b : ι} (g₁ : Y ⟶ X'' a) (g₂ : Y ⟶ X'' b)
    (hg₁ : g₁ ≫ f'' a = s) (hg₂ : g₂ ≫ f'' b = s) :
    (F.map g₁.op.toLoc).toFunctor.map
        ((Cat.Hom.toNatIso (F.mapComp' (p' a).op.toLoc (q' a).op.toLoc
          (r' a).op.toLoc (by rw [← hr']; rfl))).symm.app (T.obj a)).hom ≫
      (T.pull (p := r) (α := fun a ↦ a) (p' := r') (fun a ↦ by
        rw [← hr', Category.assoc, w, reassoc_of% w', hr])).hom s g₁ g₂ hg₁ hg₂ =
    ((T.pull (p := p) (p' := p') (f' := f') (α := fun a ↦ a) w).pull
      (p := q) (p' := q') (f' := f'') (α := fun a ↦ a) w').hom s g₁ g₂ hg₁ hg₂ ≫
      (F.map g₂.op.toLoc).toFunctor.map
        ((Cat.Hom.toNatIso (F.mapComp' (p' b).op.toLoc (q' b).op.toLoc
          (r' b).op.toLoc (by rw [← hr']; rfl))).symm.app (T.obj b)).hom := by
  change (F.map g₁.op.toLoc).toFunctor.map
      ((F.mapComp' (p' a).op.toLoc (q' a).op.toLoc (r' a).op.toLoc
        (by rw [← hr']; rfl)).inv.toNatTrans.app (T.obj a)) ≫
      pulledHom (fun a ↦ by
        rw [← hr', Category.assoc, w, reassoc_of% w', hr]) T s g₁ g₂ hg₁ hg₂ =
    pulledHom w' (T.pull (p := p) (p' := p') (f' := f')
      (α := fun a ↦ a) w) s g₁ g₂ hg₁ hg₂ ≫
      (F.map g₂.op.toLoc).toFunctor.map
        ((F.mapComp' (p' b).op.toLoc (q' b).op.toLoc (r' b).op.toLoc
          (by rw [← hr']; rfl)).inv.toNatTrans.app (T.obj b))
  rw [pulledHom_eq _ _ _ _ _ (s ≫ r) _ _ hg₁ hg₂ rfl rfl rfl,
    pulledHom_eq _ _ _ _ _ (s ≫ q) (g₁ ≫ q' a) (g₂ ≫ q' b) hg₁ hg₂ rfl rfl rfl]
  dsimp only [pull]
  rw [pulledHom_eq _ _ _ _ _ (s ≫ r) (g₁ ≫ r' a) (g₂ ≫ r' b)
    (by simp [w', reassoc_of% hg₁]) (by simp [w', reassoc_of% hg₂])
    (by rw [Category.assoc, hr]) (by rw [Category.assoc, hr'])
    (by rw [Category.assoc, hr'])]
  simp only [Category.assoc]
  rw [F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
      (p' a).op.toLoc (q' a).op.toLoc g₁.op.toLoc (r' a).op.toLoc
      (g₁ ≫ q' a).op.toLoc (g₁ ≫ r' a).op.toLoc
      (by rw [← hr']; rfl) rfl rfl,
    F.mapComp'₀₂₃_hom_app (p' b).op.toLoc (q' b).op.toLoc g₂.op.toLoc
      (r' b).op.toLoc (g₂ ≫ q' b).op.toLoc (g₂ ≫ r' b).op.toLoc
      (by rw [← hr']; rfl) rfl rfl]

set_option backward.isDefEq.respectTransparency false in
private def comparison_comp (T : F.OverlapTransitions f) {D : F.DescentData f''}
    (ε : (T.pull (p := r) (α := fun a ↦ a) (p' := r') (fun a ↦ by
      rw [← hr', Category.assoc, w, reassoc_of% w', hr])).Comparison D) :
    ((T.pull (p := p) (p' := p') (f' := f') (α := fun a ↦ a) w).pull
      (p := q) (p' := q') (f' := f'') (α := fun a ↦ a) w').Comparison D where
  e a := (Cat.Hom.toNatIso (F.mapComp' (p' a).op.toLoc (q' a).op.toLoc
    (r' a).op.toLoc (by rw [← hr']; rfl))).symm.app (T.obj a) ≪≫ ε.e a
  comm Y s a b g₁ g₂ hg₁ hg₂ := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [ε.comm]
    rw [← Category.assoc, comp_comm w w' hr hr' T s g₁ g₂ hg₁ hg₂]
    simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private def comparison_comp_inv (T : F.OverlapTransitions f) {D : F.DescentData f''}
    (ε : ((T.pull (p := p) (p' := p') (f' := f') (α := fun a ↦ a) w).pull
      (p := q) (p' := q') (f' := f'') (α := fun a ↦ a) w').Comparison D) :
    (T.pull (p := r) (α := fun a ↦ a) (p' := r') (fun a ↦ by
      rw [← hr', Category.assoc, w, reassoc_of% w', hr])).Comparison D where
  e a := (Cat.Hom.toNatIso (F.mapComp' (p' a).op.toLoc (q' a).op.toLoc
    (r' a).op.toLoc (by rw [← hr']; rfl))).app (T.obj a) ≪≫ ε.e a
  comm Y s a b g₁ g₂ hg₁ hg₂ := by
    let e₁ := (Cat.Hom.toNatIso (F.mapComp' (p' a).op.toLoc (q' a).op.toLoc
      (r' a).op.toLoc (by rw [← hr']; rfl))).symm.app (T.obj a)
    let e₂ := (Cat.Hom.toNatIso (F.mapComp' (p' b).op.toLoc (q' b).op.toLoc
      (r' b).op.toLoc (by rw [← hr']; rfl))).symm.app (T.obj b)
    have h := comp_comm w w' hr hr' T s g₁ g₂ hg₁ hg₂
    change (F.map g₁.op.toLoc).toFunctor.map e₁.hom ≫ _ =
      _ ≫ (F.map g₂.op.toLoc).toFunctor.map e₂.hom at h
    change (F.map g₁.op.toLoc).toFunctor.map (e₁.inv ≫ (ε.e a).hom) ≫ _ =
      _ ≫ (F.map g₂.op.toLoc).toFunctor.map (e₂.inv ≫ (ε.e b).hom)
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, ε.comm]
    rw [← cancel_epi ((F.map g₁.op.toLoc).toFunctor.map e₁.hom)]
    simp only [← Category.assoc, Iso.hom_inv_id_map, Category.id_comp]
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_map_assoc]

set_option backward.isDefEq.respectTransparency false in
private def comparison_pull (T : F.OverlapTransitions f) {D : F.DescentData f}
    (ε : T.Comparison D) :
    (T.pull (p := p) (p' := p') (f' := f') (α := fun a ↦ a) w).Comparison
      ((DescentData.pullFunctor F (α := fun a ↦ a) w).obj D) where
  e a := (F.map (p' a).op.toLoc).toFunctor.mapIso (ε.e a)
  comm Y s a b g₁ g₂ hg₁ hg₂ := by
    let e : T.toDescentData ε.coherent ≅ D := DescentData.isoMk ε.e ε.comm
    have h := ((DescentData.pullFunctor F (α := fun a ↦ a) w).mapIso e).hom.comm
      s g₁ g₂ hg₁ hg₂
    simpa only [e, DescentData.isoMk, DescentData.pullFunctor, Functor.mapIso_hom,
      DescentData.pullFunctorObj, DescentData.pullFunctorObjHom, toDescentData,
      pull, pulledHom, hg₁] using h

set_option backward.isDefEq.respectTransparency false in
private def comparison_postcompose (T : F.OverlapTransitions f) {D D' : F.DescentData f}
    (ε : T.Comparison D) (e : D ≅ D') : T.Comparison D' where
  e a := ε.e a ≪≫ {
    hom := e.hom.hom a
    inv := e.inv.hom a
    hom_inv_id := by
      simpa only [DescentData.comp_hom, DescentData.id_hom] using
        congrArg (fun η ↦ η.hom a) e.hom_inv_id
    inv_hom_id := by
      simpa only [DescentData.comp_hom, DescentData.id_hom] using
        congrArg (fun η ↦ η.hom a) e.inv_hom_id }
  comm Y s a b g₁ g₂ hg₁ hg₂ := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [e.hom.comm s g₁ g₂ hg₁ hg₂, ← Category.assoc, ε.comm, Category.assoc]

end CategoryTheory.Pseudofunctor.OverlapTransitions

namespace AlgebraicGeometry

/-- Refining the stage of a fixed family of overlap maps preserves its comparison
with the restriction datum on a fixed scheme. No finiteness or coherence at the
stage is required.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing); the categorical
composition calculation is Mathlib's `DescentData.pullFunctorCompIso`.
(blueprint: lem-pc-overlap-comparison-refinement).

Proof: For each chart use the pullback universal property to map its refinement
at the fixed scheme L into the original chart at L. The square expressing this
map uses p followed by r equal to p₀. Its two chart projections are uniquely
specified, so their composites agree with the direct projections. Pull the given
component isomorphism along this chart map. Compose on its source with the
pseudofunctor's composition isomorphism identifying the iterated pullback through
the later chart with pullback through the original limit chart, and on its target
with the composition isomorphism identifying the iterated restriction of M with
its restriction to the refined chart. These are all isomorphisms. On any test
scheme the comparison equation follows by pulling the original comparison
equation and using naturality of the composition isomorphisms. The associativity
coherence equation cancels the intermediate composition comparisons, exactly as
in `DescentData.pullFunctorCompIso`; identity comparisons handle the unchanged
base L. Thus the constructed component isomorphisms commute with every transition.
Empty covers have unique comparisons with vacuous component conditions. -/
theorem nonempty_overlap_comparison_refinement
    {X Y Z L : Scheme.{u}} (U : X.OpenCover.{u})
    (q₀ : Y ⟶ X) (q : Z ⟶ X) (r : Z ⟶ Y) (hr : r ≫ q₀ = q)
    (p₀ : L ⟶ Y) (p : L ⟶ Z) (hp : p ≫ r = p₀)
    (T : modulesPseudofunctor.OverlapTransitions (U.pullback₁ q₀).f)
    (M : L.Modules)
    (hcmp : Nonempty ((T.pull (p := p₀) (α := fun a ↦ a)
      (fun a ↦ Scheme.Cover.pullbackHom_map (U.pullback₁ q₀) p₀ a)).Comparison
      ((modulesPseudofunctor.toDescentData ((U.pullback₁ q₀).pullback₁ p₀).f).obj M))) :
    let V : Z.OpenCover.{u} := U.pullback₁ q
    let T' := T.pull (p := r) (α := fun a ↦ a)
      (p' := overlapRefinementHom U q₀ q r hr)
      (fun a ↦ overlapRefinementHom_map U q₀ q r hr a)
    Nonempty ((T'.pull (p := p) (α := fun a ↦ a)
      (fun a ↦ V.pullbackHom_map p a)).Comparison
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M)) := by
  classical
  intro V T'
  let V₀ : Y.OpenCover.{u} := U.pullback₁ q₀
  let W₀ : L.OpenCover.{u} := V₀.pullback₁ p₀
  let W : L.OpenCover.{u} := V.pullback₁ p
  let s := overlapRefinementHom U q₀ q r hr
  let t (a : U.I₀) : W.X a ⟶ W₀.X a :=
    pullback.lift (W.f a) (V.pullbackHom p a ≫ s a) (by
      dsimp only [s]
      rw [Category.assoc, overlapRefinementHom_map, ← Category.assoc,
        Scheme.Cover.pullbackHom_map, Category.assoc, hp])
  have ht (a : U.I₀) : t a ≫ W₀.f a = W.f a ≫ 𝟙 L := by
    change t a ≫ pullback.fst p₀ (V₀.f a) = W.f a ≫ 𝟙 L
    dsimp only [t]
    rw [pullback.lift_fst, Category.comp_id]
  have hts (a : U.I₀) :
      t a ≫ V₀.pullbackHom p₀ a = V.pullbackHom p a ≫ s a := by
    dsimp only [t, V₀]
    exact pullback.lift_snd _ _ _
  obtain ⟨ε⟩ := hcmp
  let ε₁ := CategoryTheory.Pseudofunctor.OverlapTransitions.comparison_pull
    (p := 𝟙 L) (p' := t) (f' := W.f) ht _ ε
  let e₁ := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    modulesPseudofunctor (p := 𝟙 L) (p' := t) (f' := W.f)
    (α := fun a ↦ a) ht).app M
  let e₂ := (modulesPseudofunctor.toDescentData W.f).mapIso
    ((Cat.Hom.toNatIso (modulesPseudofunctor.mapId (.mk (op L)))).app M)
  let ε₂ := CategoryTheory.Pseudofunctor.OverlapTransitions.comparison_postcompose
    _ ε₁ (e₁ ≪≫ e₂)
  let ε₃ := CategoryTheory.Pseudofunctor.OverlapTransitions.comparison_comp_inv
    (p := p₀) (q := 𝟙 L) (r := p₀)
    (p' := fun a ↦ V₀.pullbackHom p₀ a) (q' := t)
    (r' := fun a ↦ V.pullbackHom p a ≫ s a)
    (fun a ↦ V₀.pullbackHom_map p₀ a) ht (Category.id_comp _) hts T ε₂
  refine ⟨CategoryTheory.Pseudofunctor.OverlapTransitions.comparison_comp
    (p := r) (q := p) (r := p₀) (p' := s)
    (q' := fun a ↦ V.pullbackHom p a)
    (r' := fun a ↦ V.pullbackHom p a ≫ s a)
    (fun a ↦ overlapRefinementHom_map U q₀ q r hr a)
    (fun a ↦ V.pullbackHom_map p a) hp (fun _ ↦ rfl) T ε₃⟩

end AlgebraicGeometry
