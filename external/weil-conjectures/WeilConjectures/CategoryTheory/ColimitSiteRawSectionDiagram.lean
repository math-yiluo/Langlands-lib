/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # ColimitSiteRawSectionDiagram

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_precomp {A B C D : Type u} (f : A ⟶ B) (g : A ⟶ C)
    (h : Arrow.mk f = Arrow.mk g) (k : D ⟶ A) :
    Arrow.mk (k ≫ f) = Arrow.mk (k ≫ g) := by
  obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  apply (Arrow.mk_eq_mk_iff _ _).mpr
  refine ⟨rfl, hB, ?_⟩
  simp [hf, Category.assoc]

private theorem arrow_postcomp {C : Type u} [SmallCategory C]
    {S T : C ⥤ Type u} (δ : S ⟶ T) {A : Type u} {Y Z : C}
    (e : Y = Z) (f : A ⟶ S.obj Y) (g : A ⟶ S.obj Z)
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (f ≫ δ.app Y) = Arrow.mk (g ≫ δ.app Z) := by
  subst Z
  rw [Arrow.mk_injective _ _ h]

private theorem colimit_site_raw_stage_diagram
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
 :
    ∃ (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
      (β : ∀ t : Under i,
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t),
      (∀ t : Under i, (B.obj t).IsLeftKanExtension (β t)) ∧
      (∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
        Arrow.mk ((β t).app (op X) ≫
          (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
        Arrow.mk ((θ t t' b).hom.app (op X) ≫
          (β t').app (op ((F.map b.right).toFunctor.obj X)))) := by
  let A (t : Under i) := (sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let f {t t' : Under i} (b : t ⟶ t') := (F.map b.right).toFunctor
  let v (t : Under i) := (V.ι.app t.right).toFunctor
  have ev {t t' : Under i} (b : t ⟶ t') : f b ⋙ v t' = v t :=
    congrArg Cat.Hom.toFunctor (V.w b.right)
  have ef {t t' : Under i} (b : t ⟶ t') :
      (F.map t.hom).toFunctor ⋙ f b = (F.map t'.hom).toFunctor :=
    congrArg Cat.Hom.toFunctor
      ((F.map_comp t.hom b.right).symm.trans (congrArg F.map (Under.w b)))
  have eid (t : Under i) : f (𝟙 t) = 𝟭 (F.obj t.right) :=
    congrArg Cat.Hom.toFunctor (F.map_id t.right)
  have ecomp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      f b ⋙ f c = f (b ≫ c) :=
    congrArg Cat.Hom.toFunctor (F.map_comp b.right c.right).symm
  have hid (t : Under i) :
      (θ t t (𝟙 t)).hom ≫
        eqToHom (congrArg
          (fun (g : F.obj t.right ⥤ F.obj t.right) ↦ g.op ⋙ (A t).obj) (eid t)) =
      𝟙 (A t).obj := by
    let k : A t ⟶ A t :=
      ⟨(θ t t (𝟙 t)).hom ≫
        eqToHom (congrArg (fun (g : F.obj t.right ⥤ F.obj t.right) ↦ g.op ⋙ (A t).obj) (eid t))⟩
    suffices hk : k = 𝟙 (A t) from congrArg (fun a ↦ a.hom) hk
    apply ((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    simpa [k, A, NatTrans.comp_app, eqToHom_app, ← Category.assoc] using hθ t t (𝟙 t) X.unop
  have hcomp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      (θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (θ t' t'' c).hom ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ (A t'').obj) (ecomp b c)) =
      (θ t t'' (b ≫ c)).hom := by
    let k : A t ⟶ ((f (b ≫ c)).sheafPushforwardContinuous (Type u)
        (P t.right).toGrothendieck (P t''.right).toGrothendieck).obj (A t'') :=
      ⟨(θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (θ t' t'' c).hom ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ (A t'').obj) (ecomp b c))⟩
    suffices hk : k = θ t t'' (b ≫ c) from congrArg (fun a ↦ a.hom) hk
    apply ((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    have he : op ((f b).obj ((F.map t.hom).toFunctor.obj X.unop)) =
        op ((F.map t'.hom).toFunctor.obj X.unop) :=
      congrArg (fun g ↦ op (g.obj X.unop)) (ef b)
    have ht := arrow_postcomp (θ t' t'' c).hom he _ _ (hθ t t' b X.unop)
    simpa [k, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, ← Category.assoc]
      using ht.trans ((hθ t' t'' c X.unop).trans (hθ t t'' (b ≫ c) X.unop).symm)
  let R (t : Under i) := (v t).op.leftKanExtension (A t).obj
  let β (t : Under i) : (A t).obj ⟶ (v t).op ⋙ R t := (v t).op.leftKanExtensionUnit (A t).obj
  let m {t t' : Under i} (b : t ⟶ t') : R t ⟶ R t' :=
    (R t).descOfIsLeftKanExtension (β t) (R t')
      ((θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (β t') ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ R t') (ev b)))
  have hm {t t' : Under i} (b : t ⟶ t') :
      β t ≫ Functor.whiskerLeft (v t).op (m (t := t) (t' := t') b) =
      (θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (β t') ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ R t') (ev b)) :=
    (R t).descOfIsLeftKanExtension_fac (β t) _ _
  have hmap {t t' : Under i} (b : t ⟶ t') (X : F.obj t.right) :
      Arrow.mk ((β t).app (op X) ≫ (m b).app (op ((v t).obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫ (β t').app (op ((f b).obj X))) := by
    have h := NatTrans.congr_app (hm b) (op X)
    simpa [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, ← Category.assoc]
      using congrArg Arrow.mk h
  have hmid (t : Under i) : m (𝟙 t) = 𝟙 (R t) := by
    apply (R t).hom_ext_of_isLeftKanExtension (β t)
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    have hi : Arrow.mk ((θ t t (𝟙 t)).hom.app X) =
        Arrow.mk (𝟙 ((A t).obj.obj X)) := by
      have h := congrArg Arrow.mk (NatTrans.congr_app (hid t) X)
      simpa [NatTrans.comp_app, eqToHom_app] using h
    have ht := arrow_postcomp (β t)
      (congrArg (fun g ↦ g.op.obj X) (eid t)) _ _ hi
    simpa [A, β] using (hmap (𝟙 t) X.unop).trans ht
  have hmcomp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      m (t := t) (t' := t'') (b ≫ c) =
      m (t := t) (t' := t') b ≫ m (t := t') (t' := t'') c := by
    apply (R t).hom_ext_of_isLeftKanExtension (β t)
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    have he : op ((v t).obj X.unop) = op ((v t').obj ((f b).obj X.unop)) :=
      congrArg (fun g ↦ op (g.obj X.unop)) (ev b).symm
    have h1 := arrow_postcomp (m (t := t') (t' := t'') c) he _ _ (hmap b X.unop)
    have h2 := arrow_precomp _ _ (hmap c ((f b).obj X.unop))
      ((θ t t' b).hom.app X)
    have ht : Arrow.mk ((θ t t' b).hom.app X ≫
        (θ t' t'' c).hom.app ((f b).op.obj X)) =
        Arrow.mk ((θ t t'' (b ≫ c)).hom.app X) := by
      have h := congrArg Arrow.mk (NatTrans.congr_app (hcomp b c) X)
      simpa [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, ← Category.assoc]
        using h
    have h3 := arrow_postcomp (β t'')
      (congrArg (fun g ↦ g.op.obj X) (ecomp b c)) _ _ ht
    have h4 := (h1.trans (h2.trans h3)).trans (hmap (b ≫ c) X.unop).symm
    simpa [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using h4.symm
  let B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u) :=
    { obj := R
      map := fun b ↦ m b
      map_id := hmid
      map_comp := hmcomp }
  exact ⟨B, β, fun t ↦ inferInstance, fun t t' b X ↦ hmap b X⟩

private theorem colimit_site_raw_comparison_unit_compatibility
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
      (β : ∀ t : Under i,
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (δ : ∀ t : Under i, B.obj t ⟶
      ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj)
    (hδ : ∀ (t : Under i) (X : F.obj t.right),
      (β t).app (op X) ≫
        (δ t).app (op ((V.ι.app t.right).toFunctor.obj X)) =
      (α t).hom.app (op X)) :
    ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      (β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X)) ≫
        (δ t').app (op ((V.ι.app t.right).toFunctor.obj X)) =
      (α t).hom.app (op X) := by
  intro t t' b
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let c : (sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
        (P t.right).toGrothendieck Q.toGrothendieck).obj H :=
    ⟨β t ≫ Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (B.map b ≫ δ t')⟩
  have eV (X : F.obj t.right) :
      op ((V.ι.app t.right).toFunctor.obj X) =
      op ((V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj X)) := by
    have e := congrArg Cat.Hom.toFunctor (V.w b.right)
    exact congrArg (fun f ↦ op (f.obj X)) e.symm
  have eF (X : F.obj i) :
      op ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X)) =
      op ((F.map t'.hom).toFunctor.obj X) := by
    have e := congrArg Cat.Hom.toFunctor
      ((F.map_comp t.hom b.right).symm.trans (congrArg F.map (Under.w b)))
    exact congrArg (fun f ↦ op (f.obj X)) e
  have hc : c = α t := by
    apply ((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    change Arrow.mk (_ ≫ (c.hom.app (op ((F.map t.hom).toFunctor.obj X.unop)))) =
      Arrow.mk (_ ≫ ((α t).hom.app (op ((F.map t.hom).toFunctor.obj X.unop))))
    have hm := arrow_postcomp (δ t') (eV ((F.map t.hom).toFunctor.obj X.unop))
      _ _ (hβmap t t' b ((F.map t.hom).toFunctor.obj X.unop))
    have hm' := arrow_precomp _ _ hm
      (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app X)
    have ht := arrow_postcomp (α t').hom (eF X.unop) _ _ (hθ t t' b X.unop)
    simp only [Category.assoc] at hm' ht
    rw [hδ t' ((F.map b.right).toFunctor.obj
      ((F.map t.hom).toFunctor.obj X.unop))] at hm'
    exact hm'.trans (ht.trans ((hα t' X.unop).trans (hα t X.unop).symm))
  intro X
  exact NatTrans.congr_app (congrArg (fun k ↦ k.hom) hc) (op X)


/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-diagram).

Proof: Construct B(t) as the left Kan extension of the underlying stage inverse-image
sheaf along V(t.right).op, and β(t) as its universal unit. For b : t to t',
compose θ(b) with β(t') and transport along V.w; the Kan universal property
constructs B.map b. Adjunction uniqueness under hθ proves identities and
composition. Extend α(t) by the same Kan property to γ(t); hα and hθ prove
naturality. This constructs the raw diagram and its comparison maps only;
no sheaf condition or isomorphism after sheafification is asserted here.
The universal units determine B, its maps and γ up to the unique compatible
isomorphism; no arbitrary existence witness is used to define an object.
-/
theorem colimit_site_raw_section_diagram
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
 :
    ∃ (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
      (β : ∀ t : Under i,
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
      (γ : B ⟶ (Functor.const (Under i)).obj
        ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj),
      (∀ t : Under i, (B.obj t).IsLeftKanExtension (β t)) ∧
      (∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
        Arrow.mk ((β t).app (op X) ≫
          (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
        Arrow.mk ((θ t t' b).hom.app (op X) ≫
          (β t').app (op ((F.map b.right).toFunctor.obj X)))) ∧
      (∀ (t : Under i) (X : F.obj t.right),
        (β t).app (op X) ≫
          (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj X)) =
        (α t).hom.app (op X)) := by
  obtain ⟨B, β, hβ, hβmap⟩ :=
    colimit_site_raw_stage_diagram J F P V Q i G θ hθ
  let (t : Under i) : (B.obj t).IsLeftKanExtension (β t) := hβ t
  let H := ((sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G).obj
  let δ : ∀ t : Under i, B.obj t ⟶ H := fun t ↦
    (B.obj t).descOfIsLeftKanExtension (β t) H (α t).hom
  have hδ (t : Under i) (X : F.obj t.right) :
      (β t).app (op X) ≫
        (δ t).app (op ((V.ι.app t.right).toFunctor.obj X)) =
      (α t).hom.app (op X) :=
    (B.obj t).descOfIsLeftKanExtension_fac_app (β t) H (α t).hom (op X)
  have hc := colimit_site_raw_comparison_unit_compatibility
    J F P V Q i G α hα θ hθ B β hβmap δ hδ
  let γ : B ⟶ (Functor.const (Under i)).obj H :=
    { app := δ
      naturality := by
        intro t t' b
        change B.map b ≫ δ t' = δ t ≫ 𝟙 H
        rw [Category.comp_id]
        apply (B.obj t).hom_ext_of_isLeftKanExtension (β t)
        apply NatTrans.ext
        funext X
        simpa [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
          using (hc t t' b X.unop).trans (hδ t X.unop).symm }
  exact ⟨B, β, γ, hβ, hβmap, hδ⟩


end CategoryTheory
