/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentRelativeProfiniteSite
public import WeilConjectures.AlgebraicGeometry.Affine.AffineComponentSiteProjection
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Topology.InverseImageStalk

/-!
# The relative component lift as a locally ringed topological pullback

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 2.2.8 and its proof, printed p. 10

## Implementation details

The two functors are the witnesses of the recorded construction theorems. Their
universal and geometric characterizations determine them up to unique isomorphism
preserving both coordinates. The sheaf clause uses the actual structure-map adjunct.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem pullback_structure_sheaf_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x : X, IsIso (f.stalkMap x)) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
      Y.sheaf X.sheaf).symm ⟨f.c⟩) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base
  let a := (adj.homEquiv Y.sheaf X.sheaf).symm ⟨f.c⟩
  have hu : adj.unit.app Y.sheaf ≫ (TopCat.Sheaf.pushforward _ f.base).map a =
      ⟨f.c⟩ := (adj.homEquiv Y.sheaf X.sheaf).apply_symm_apply ⟨f.c⟩
  have (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map a.hom) := by
    obtain ⟨c, hc, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing f.base x
    have he : (c.app Y.sheaf).hom ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map a.hom = f.stalkMap x := by
      apply TopCat.Presheaf.stalk_hom_ext
      intro V hx
      have hcV : TopCat.Presheaf.germ Y.presheaf V (f x) hx ≫ (c.app Y.sheaf).hom =
          ((adj.unit.app Y.sheaf).hom.app (Opposite.op V)) ≫
            TopCat.Presheaf.germ ((TopCat.Sheaf.pullback _ f.base).obj Y.sheaf).obj
              ((TopologicalSpace.Opens.map f.base).obj V) x hx := by
        ext s
        exact hc Y.sheaf V hx s
      change (Y.presheaf.germ V (f x) hx ≫ (c.app Y.sheaf).hom) ≫ _ = _
      erw [hcV, Category.assoc,
        TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc]
      have huV := congrArg (fun q ↦ q.hom.app (Opposite.op V)) hu
      change (adj.unit.app Y.sheaf).hom.app (Opposite.op V) ≫
        a.hom.app (Opposite.op ((TopologicalSpace.Opens.map f.base).obj V)) =
          f.c.app (Opposite.op V) at huV
      rw [huV]
      exact (f.germ_stalkMap V x hx).symm
    have := hf x
    have : IsIso ((c.app Y.sheaf).hom ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map a.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (c.app Y.sheaf).hom _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso a

private theorem components_homeomorph {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) :
    ∃ e : ConnectedComponents X ≃ₜ ConnectedComponents Y,
      ∀ x : X, e (ConnectedComponents.mk x) = ConnectedComponents.mk (h x) := by
  refine ⟨{
    toFun := h.continuous.connectedComponentsMap
    invFun := h.symm.continuous.connectedComponentsMap
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := h.continuous.connectedComponentsMap_continuous
    continuous_invFun := h.symm.continuous.connectedComponentsMap_continuous }, fun _ ↦ rfl⟩
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (h.symm (h x)) = ConnectedComponents.mk x
    rw [h.symm_apply_apply]
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (h (h.symm x)) = ConnectedComponents.mk x
    rw [h.apply_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- The two chosen construction witnesses have large specifications; keep them folded.
/-- The inverse limit of finite clopen stages is naturally the component-site scheme.
Its topological space is the subspace pullback, its structure sheaf is the inverse
image under the first projection, and its components are the second coordinate. -/
theorem relative_component_lift_pullback_space (T : Scheme.{u}) [IsAffine T] :
    ∃ θ : ((component_relative_profinite_site T).choose ⋙ Scheme.ProEt.forget T) ≅
        ((Scheme.ProEt.affine_component_site_projection T).choose ⋙ Scheme.ProEt.forget T),
      (∀ (E : Over (affineComponentSpace T))
        (x : ((component_relative_profinite_site T).choose.obj E).left),
        (Scheme.ProEt.affine_component_site_projection T).choose_spec.choose E
            ((θ.hom.app E).left x) =
          (component_relative_profinite_site T).choose_spec.2.1.choose E x) ∧
      ∃ H : ∀ E : Over (affineComponentSpace T),
          ((component_relative_profinite_site T).choose.obj E).left ≃ₜ
            {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ (E : Over (affineComponentSpace T))
          (x : ((component_relative_profinite_site T).choose.obj E).left),
          (H E x).val.1 = ((component_relative_profinite_site T).choose.obj E).hom x ∧
          (H E x).val.2 =
            (component_relative_profinite_site T).choose_spec.2.1.choose E x) ∧
        (∀ E : Over (affineComponentSpace T),
          IsIso
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
              ((component_relative_profinite_site T).choose.obj E).hom.base).homEquiv
                T.sheaf ((component_relative_profinite_site T).choose.obj E).left.sheaf).symm
              ⟨((component_relative_profinite_site T).choose.obj E).hom.c⟩)) ∧
        (∀ (E : Over (affineComponentSpace T))
          (x : ((component_relative_profinite_site T).choose.obj E).left),
          IsIso (((component_relative_profinite_site T).choose.obj E).hom.stalkMap x)) ∧
        (∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E')
          (x : ((component_relative_profinite_site T).choose.obj E).left),
          (H E' (((component_relative_profinite_site T).choose.map a).left x)).val =
            ((H E x).val.1, a.left (H E x).val.2)) ∧
        ∀ E : Over (affineComponentSpace T),
          ∃ e : ConnectedComponents
              ((component_relative_profinite_site T).choose.obj E).left ≃ₜ E.left,
            ∀ x : ((component_relative_profinite_site T).choose.obj E).left,
              e (ConnectedComponents.mk x) = (H E x).val.2 := by
  classical
  let F := (component_relative_profinite_site T).choose
  let p := (component_relative_profinite_site T).choose_spec.2.1.choose
  have hp := (component_relative_profinite_site T).choose_spec.2.1.choose_spec
  let U : Over (affineComponentSpace T) ⥤ T.ProEt :=
    (Scheme.ProEt.affine_component_site_projection T).choose
  let r : ∀ E : Over (affineComponentSpace T), C((U.obj E).left, E.left) :=
    (Scheme.ProEt.affine_component_site_projection T).choose_spec.choose
  have hU := (Scheme.ProEt.affine_component_site_projection T).choose_spec.choose_spec
  -- Direct projections avoid reducing the large chosen specifications during destructuring.
  have hUmapping := component_mapping_property T U r
    (fun E ↦ ⟨(hU.1 E).2.2.1, (hU.1 E).2.2.2.1⟩)
  have hr := hUmapping.1
  have hmapU := hUmapping.2
  let L := F ⋙ Scheme.ProEt.forget T
  let M := U ⋙ Scheme.ProEt.forget T
  have extL (W : Over T) (E : Over (affineComponentSpace T))
      (a b : W ⟶ L.obj E) (hab : ∀ w, p E (a.left w) = p E (b.left w)) : a = b := by
    let g : C(W.left, E.left) := (p E).comp ⟨b.left, b.left.continuous⟩
    have hg (w : W.left) : E.hom (g w) = ConnectedComponents.mk (W.hom w) :=
      (hp.1 E _).trans (congrArg ConnectedComponents.mk (congrArg (fun l ↦ l w) b.w))
    exact (hp.2.2 W E g hg).unique hab (fun _ ↦ rfl)
  have extM (W : Over T) (E : Over (affineComponentSpace T))
      (a b : W ⟶ M.obj E) (hab : ∀ w, r E (a.left w) = r E (b.left w)) : a = b := by
    let g : C(W.left, E.left) := (r E).comp ⟨b.left, b.left.continuous⟩
    have hg (w : W.left) : E.hom (g w) = ConnectedComponents.mk (W.hom w) :=
      (hr E _).trans (congrArg ConnectedComponents.mk (congrArg (fun l ↦ l w) b.w))
    exact (hmapU W E g hg).unique hab (fun _ ↦ rfl)
  -- The public universal properties already incorporate the finite-stage construction.
  choose f hf using fun E ↦ ExistsUnique.exists (hmapU (L.obj E) E (p E) (hp.1 E))
  choose g hg using fun E : Over (affineComponentSpace T) ↦
    ExistsUnique.exists (hp.2.2 (M.obj E) E (r E) (hr E))
  let e (E : Over (affineComponentSpace T)) : L.obj E ≅ M.obj E :=
    { hom := f E
      inv := g E
      hom_inv_id := by
        apply extL
        intro x
        change p E ((g E).left ((f E).left x)) = p E x
        exact (hg E _).trans (hf E x)
      inv_hom_id := by
        apply extM
        intro x
        change r E ((f E).left ((g E).left x)) = r E x
        exact (hf E _).trans (hg E x) }
  let θ : L ≅ M := NatIso.ofComponents e (by
    intro E E' a
    apply extM
    intro x
    change r E' ((f E').left ((F.map a).left x)) =
      r E' ((U.map a).left ((f E).left x))
    exact (hf E' _).trans ((hp.2.1 E E' a x).trans
      ((congrArg a.left (hf E x).symm).trans (hU.2.1 E E' a _).symm)))
  refine ⟨θ, hf, ?_⟩
  choose h ht hs using fun E ↦ (hU.1 E).2.2.2.1
  let eS (E : Over (affineComponentSpace T)) := (Over.forget T).mapIso (e E)
  let H (E : Over (affineComponentSpace T)) := (Scheme.homeoOfIso (eS E)).trans (h E)
  have hH (E : Over (affineComponentSpace T)) (x : (F.obj E).left) :
      (H E x).val.1 = (F.obj E).hom x ∧ (H E x).val.2 = p E x := by
    constructor
    · exact (ht E _).trans (congrArg (fun l ↦ l x) (f E).w)
    · exact (hs E _).trans (hf E x)
  have hstalk (E : Over (affineComponentSpace T)) (x : (F.obj E).left) :
      IsIso ((F.obj E).hom.stalkMap x) := by
    have := (hU.1 E).2.2.1 ((f E).left x)
    have : IsIso ((f E).left) := (eS E).isIso_hom
    have hcomp : (F.obj E).hom = (f E).left ≫ (U.obj E).hom := (f E).w.symm
    rw [hcomp, Scheme.Hom.stalkMap_comp]
    infer_instance
  refine ⟨H, hH, fun E ↦ pullback_structure_sheaf_isIso _ (hstalk E), hstalk, ?_, ?_⟩
  · intro E E' a x
    apply Prod.ext
    · exact (hH E' _).1.trans
        ((congrArg (fun l ↦ l x) (F.map a).w).trans (hH E x).1.symm)
    · exact (hH E' _).2.trans ((hp.2.1 E E' a x).trans
        (congrArg a.left (hH E x).2.symm))
  · intro E
    obtain ⟨c, hc⟩ := components_homeomorph (Scheme.homeoOfIso (eS E))
    obtain ⟨d, hd⟩ := (hU.1 E).2.2.2.2
    refine ⟨c.trans d, ?_⟩
    intro x
    exact (congrArg d (hc x)).trans ((hd _).trans (hs E _).symm)

end AlgebraicGeometry.ProEtale
