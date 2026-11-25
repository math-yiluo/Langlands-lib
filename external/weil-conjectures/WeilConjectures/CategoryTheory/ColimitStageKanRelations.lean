/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ColimitSiteKanUnitRelations

/-! # Eventual equality of stagewise Kan representatives

Source: Stacks Project, Sites, Tag 0A35, arbitrary-object section formula.
(blueprint: lem-weil-pbc-colimit-stage-kan-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of two stage sections in the raw Kan colimit holds at a common refinement.
This is only the relation calculation; it does not assert existence of representatives
or a colimit universal property.

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
arbitrary-object section formula and its independence of choices.
(blueprint: lem-weil-pbc-colimit-stage-kan-relations).

Proof: Write S = Under.map(a). This functor is final: for any t in Under i,
choose a common successor of t.right and k, then equalize the two maps from i.
This gives an arrow t -> S(r). Parallel arrows into S(r) are equalized by a
further stage refinement of r. Mathlib's filtered finality criterion applies.
Thus the outer colimit B can also be evaluated over Under k via S.

At U, put Y = V_j(U) and X_r = F(b followed by r.hom)(U). Normalize the stage
map e_r followed by beta_(S(r)) to Y with the equality transport from V.w.
The formula hbeta_map, hD, and naturality along equality transports show that
these normalized maps intertwine D transitions with B(S(c)). Naturality of the
outer colimit coprojections and hnu identify the cocone maps with the normalized
maps followed by those coprojections. Evaluation preserves colimits. Its
filtered-set equality criterion now moves x and x' to a common r in Under k
where their normalized beta-unit images agree. Cancel the invertible endpoint
transport to obtain equality under beta_(S(r)) at X_r.

Apply raw_section_kan_unit_relations with base k, stage r, presheaves A_(S(q))
and transition maps theta_(S(r),S(q),S(d)). That existing lemma lifts a finite
zigzag of Kan relations to a later q and gives equality of the two theta images.
The formula hD transports this equality to equality under e_q of the two
D-transitions. Its component is an isomorphism, so cancellation gives equality
of D sections. Functoriality of D combines each original transition with d.
No generator-existence theorem or comparison universal property is used.
The identity and composition hypotheses remain in the interface but are not
needed by this reduction.
-/
theorem stage_kan_cocone_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (hθid : ∀ (t : Under i) (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t (𝟙 t)).app X) = Arrow.mk (𝟙 ((A t).obj X)))
    (hθcomp : ∀ (t t' t'' : Under i) (c : t ⟶ t') (d : t' ⟶ t'')
        (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t' c).app X ≫
        (θ t' t'' d).app ((F.map c.right).toFunctor.op.obj X)) =
      Arrow.mk ((θ t t'' (c ≫ d)).app X))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ Type u))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (hD : ∀ (t t' : Under k) (c : t ⟶ t') (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((D.map c).app U ≫ (e t').hom.app U) =
      Arrow.mk ((e t).hom.app U ≫
        (θ ((Under.map a).obj t) ((Under.map a).obj t') ((Under.map a).map c)).app
          ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))) :
    ∀ (U : (F.obj j)ᵒᵖ) (t t' : Under k)
      (x : (D.obj t).obj U) (x' : (D.obj t').obj U),
      (ν.ι.app t).app U x = (ν.ι.app t').app U x' →
        ∃ (r : Under k) (c : t ⟶ r) (c' : t' ⟶ r),
          (D.map c).app U x = (D.map c').app U x' := by
  classical
  -- Keep the original coherence hypotheses in this interface; the reduction needs neither.
  have _ := hθid
  have _ := hθcomp
  let S := Under.map a
  have : S.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro t
      let l := IsFiltered.max t.right k
      let p : t.right ⟶ l := IsFiltered.leftToMax _ _
      let q : k ⟶ l := IsFiltered.rightToMax _ _
      let z := IsFiltered.coeqHom (t.hom ≫ p) (a ≫ q)
      refine ⟨Under.mk (q ≫ z), ⟨Under.homMk (p ≫ z) ?_⟩⟩
      simpa only [S, Under.map_obj_hom, Under.mk_hom, Category.assoc] using
        IsFiltered.coeq_condition (t.hom ≫ p) (a ≫ q)
    · intro t r f g
      let z := IsFiltered.coeqHom f.right g.right
      refine ⟨Under.mk (r.hom ≫ z), Under.homMk z (by simp), ?_⟩
      apply Under.UnderMorphism.ext
      exact IsFiltered.coeq_condition f.right g.right
  rcases ν with ⟨pt, ι⟩
  dsimp only at hpt
  subst pt
  intro U t t' x x' h
  let Y := (V.ι.app j).toFunctor.op.obj U
  let X (r : Under k) := (F.map (b ≫ r.hom)).toFunctor.op.obj U
  have hv (r : Under k) :
      (V.ι.app r.right).toFunctor.op.obj (X r) = Y :=
    congrArg (fun f : F.obj j ⟶ V.pt ↦ f.toFunctor.op.obj U) (V.w (b ≫ r.hom))
  let f (r : Under k) : (D.obj r).obj U ⟶ (B.obj (S.obj r)).obj Y :=
    (e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
      eqToHom (congrArg (B.obj (S.obj r)).obj (hv r))
  have hf (r r' : Under k) (c : r ⟶ r') :
      f r ≫ (B.map (S.map c)).app Y = (D.map c).app U ≫ f r' := by
    have hu : (F.map c.right).toFunctor.op.obj (X r) = X r' := by
      dsimp [X]
      rw [← Functor.comp_obj, ← Cat.Hom.comp_toFunctor, ← F.map_comp]
      rw [Category.assoc, Under.w c]
    have hb := hβmap (S.obj r) (S.obj r') (S.map c) (X r).unop
    have hp : Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
        (B.map (S.map c)).app ((V.ι.app r.right).toFunctor.op.obj (X r))) =
        Arrow.mk ((e r).hom.app U ≫ (θ (S.obj r) (S.obj r') (S.map c)).app
          (X r) ≫ (β (S.obj r')).app ((F.map c.right).toFunctor.op.obj (X r))) := by
      obtain ⟨_, he, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp hb
      simp only [Functor.op_obj, op_unop, S, Under.map_obj_right,
        Under.map_map_right] at he hh ⊢
      rw [hh]
      simp only [eqToHom_refl, Category.id_comp]
      simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    have hd := hD r r' c U
    have hpost : Arrow.mk ((D.map c).app U ≫ (e r').hom.app U ≫
        (β (S.obj r')).app (X r')) =
        Arrow.mk ((e r).hom.app U ≫ (θ (S.obj r) (S.obj r') (S.map c)).app
          (X r) ≫ (β (S.obj r')).app ((F.map c.right).toFunctor.op.obj (X r))) := by
      have post : ∀ {Z Z' : (F.obj r'.right)ᵒᵖ} (hz : Z = Z')
          (v : (D.obj r).obj U ⟶ (A (S.obj r')).obj Z)
          (v' : (D.obj r).obj U ⟶ (A (S.obj r')).obj Z'),
          Arrow.mk v = Arrow.mk v' →
          Arrow.mk (v ≫ (β (S.obj r')).app Z) =
            Arrow.mk (v' ≫ (β (S.obj r')).app Z') := by
        intro Z Z' hz v v' hh
        subst Z'
        rw [Arrow.mk_injective _ _ hh]
      simpa only [Category.assoc] using post hu.symm _ _ hd
    have hn := (B.map (S.map c)).naturality (eqToHom (hv r))
    simp only [eqToHom_map] at hn
    apply Arrow.mk_injective
    calc
      Arrow.mk (f r ≫ (B.map (S.map c)).app Y) =
          Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
            (B.map (S.map c)).app
              ((V.ι.app r.right).toFunctor.op.obj (X r))) := by
        dsimp [f]
        rw [Category.assoc, Category.assoc, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Functor.op_obj]
      _ = Arrow.mk ((D.map c).app U ≫ (e r').hom.app U ≫
          (β (S.obj r')).app (X r')) := hp.trans hpost.symm
      _ = Arrow.mk ((D.map c).app U ≫ f r') := by
        dsimp [f]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  have hk (r : Under k) : (ι.app r).app U = f r ≫ (colimit.ι B (S.obj r)).app Y := by
    have hn := (colimit.ι B (S.obj r)).naturality (eqToHom (hv r))
    simp only [eqToHom_map] at hn
    apply Arrow.mk_injective
    calc
      Arrow.mk ((ι.app r).app U) =
          Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
            (colimit.ι B (S.obj r)).app
              ((V.ι.app r.right).toFunctor.op.obj (X r))) := hν r U
      _ = Arrow.mk (f r ≫ (colimit.ι B (S.obj r)).app Y) := by
        dsimp [f]
        rw [Category.assoc, Category.assoc, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Functor.op_obj]
  let ev := (evaluation V.ptᵒᵖ (Type u)).obj Y
  have hc := (Functor.Final.isColimitWhiskerEquiv S _).symm
    (isColimitOfPreserves ev (colimit.isColimit B))
  have hh : ((ev.mapCocone (colimit.cocone B)).whisker S).ι.app t (f t x) =
      ((ev.mapCocone (colimit.cocone B)).whisker S).ι.app t' (f t' x') := by
    rw [hk t, hk t'] at h
    exact h
  obtain ⟨r, c, c', hr⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (S ⋙ B ⋙ ev) hc).mp hh
  have hfr : f r ((D.map c).app U x) = f r ((D.map c').app U x') :=
    (ConcreteCategory.congr_hom (hf t r c) x).symm.trans
      (hr.trans (ConcreteCategory.congr_hom (hf t' r c') x'))
  have hbr : (β (S.obj r)).app (X r) ((e r).hom.app U ((D.map c).app U x)) =
      (β (S.obj r)).app (X r) ((e r).hom.app U ((D.map c').app U x')) :=
    (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (B.obj (S.obj r)).obj (hv r)))).1 hfr
  obtain ⟨q, d, hd⟩ := raw_section_kan_unit_relations J F V hobjects harrows k r
    (fun q ↦ A (S.obj q)) (fun q d ↦ θ (S.obj r) (S.obj q) (S.map d))
    (B.obj (S.obj r)) (β (S.obj r)) (hβ (S.obj r)) (X r).unop
    ((e r).hom.app U ((D.map c).app U x))
    ((e r).hom.app U ((D.map c').app U x')) hbr
  refine ⟨q, c ≫ d, c' ≫ d, ?_⟩
  obtain ⟨_, he, hm⟩ := (Arrow.mk_eq_mk_iff _ _).mp (hD r q d U)
  have hx := ConcreteCategory.congr_hom hm ((D.map c).app U x)
  have hx' := ConcreteCategory.congr_hom hm ((D.map c').app U x')
  have hdd : (D.map d).app U ((D.map c).app U x) =
      (D.map d).app U ((D.map c').app U x') := by
    apply (ConcreteCategory.bijective_of_isIso ((e q).hom.app U)).1
    have ht := congrArg (fun z ↦ (eqToHom he.symm) z) hd
    simpa only [types_comp_apply, eqToHom_refl, types_id_apply] using
      hx.trans (ht.trans hx'.symm)
  simpa only [D.map_comp, NatTrans.comp_app, types_comp_apply] using hdd

end CategoryTheory
