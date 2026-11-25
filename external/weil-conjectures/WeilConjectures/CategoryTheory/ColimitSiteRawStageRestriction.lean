/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import WeilConjectures.CategoryTheory.ColimitStageKanCocone

/-! # Stage restriction of the raw Kan colimit

Source: Stacks Project, Sites, Tag 0A35, section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-stage-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_postcomp {C : Type*} [Category C] {D : Type*} [Category D]
    {S T : C ⥤ D} (δ : S ⟶ T) {A : D} {Y Z : C}
    (e : Y = Z) (f : A ⟶ S.obj Y) (g : A ⟶ S.obj Z)
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (f ≫ δ.app Y) = Arrow.mk (g ≫ δ.app Z) := by
  subst Z
  rw [Arrow.mk_injective _ _ h]


private theorem arrow_transport_comp {C : Type u} [SmallCategory C]
    {S T : C ⥤ Type u} (δ : S ⟶ T) {Z : Type u} {X Y : C}
    (e : X = Y) (p : Z ⟶ S.obj X) :
    Arrow.mk ((p ≫ eqToHom (congrArg S.obj e)) ≫ δ.app Y) =
      Arrow.mk (p ≫ δ.app X) := by
  subst Y
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of the raw presheaf to any stage is a filtered presheaf colimit
of stage sheaves. This comparison uses no finiteness assumption on covering presieves.
Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-stage-restriction).

Proof: Choose a common stage k receiving i and j by filteredness, with arrows a and b.
For t in Under k, pull G to t.right along a followed by t.hom, and push this sheaf
back to stage j along b followed by t.hom. These are the objects D(t). Along a
morphism of Under k, use the adjunction transpose of the unit to define the
transition. Uniqueness of adjunction transposes proves the identity and composition
laws. The hypothesis htheta identifies these transitions with the supplied theta.

At an object U of stage j, the Kan unit beta followed by the outer coprojection
maps a section of D(t) to the raw colimit at V(j)(U), using the cocone equality to
identify V(t.right)(F(b followed by t.hom)(U)) with V(j)(U). Naturality of beta,
hbeta_map, and the coprojection equations make these maps a cocone and natural in U.
Every Kan generator at V(j)(U) is a stage section paired with an arrow from V(j)(U)
to a stage image. Represent that arrow and its endpoints in the object and arrow
set colimits, move to a stage receiving k and the generator's stage, and equalize
the arrows from k. Restriction along the lifted arrow gives a D representative.
Thus the induced comparison is surjective. Any equality of generators is a finite
chain of Kan and outer-colimit relations. Lift all arrows and equations in this
chain to one later stage, using the filtered-set eventual-equality criterion.
Naturality and hbeta_map identify each relation with a section restriction or the
transition of D. Therefore the two D representatives agree at a further stage,
proving injectivity. These inverse bijections are natural in U, and define the
presheaf isomorphism q. The specified object isomorphisms are identities for this
construction. No finite cover, amalgamation, or separatedness is used here.
-/
theorem colimit_site_raw_stage_restriction
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
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
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) :
    ∃ (k : J) (a : i ⟶ k) (b : j ⟶ k)
      (D : Under k ⥤ Sheaf (P j).toGrothendieck (Type u)),
      Nonempty (colimit (D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)) ≅
        (V.ι.app j).toFunctor.op ⋙ colimit B) ∧
      ∀ t : Under k, Nonempty (D.obj t ≅
        ((F.map (b ≫ t.hom)).toFunctor.sheafPushforwardContinuous (Type u)
          (P j).toGrothendieck (P t.right).toGrothendieck).obj
          ((sheafPullback (F.map (a ≫ t.hom)).toFunctor (Type u)
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G)) := by
  classical
  let A (t : Under i) := (sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let f {t t' : Under i} (b : t ⟶ t') := (F.map b.right).toFunctor
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
  obtain ⟨k, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs i j
  let s := Under.map a
  let g (t : Under k) := (F.map (b ≫ t.hom)).toFunctor
  have eg {t t' : Under k} (c : t ⟶ t') :
      g t ⋙ f (s.map c) = g t' := by
    exact congrArg Cat.Hom.toFunctor
      ((F.map_comp (b ≫ t.hom) c.right).symm.trans
        (congrArg F.map (by rw [Category.assoc, Under.w c])))
  let R (t : Under k) := ((g t).sheafPushforwardContinuous (Type u)
    (P j).toGrothendieck (P t.right).toGrothendieck).obj (A (s.obj t))
  let m {t t' : Under k} (c : t ⟶ t') : R t ⟶ R t' :=
    ⟨Functor.whiskerLeft (g t).op (θ (s.obj t) (s.obj t') (s.map c)).hom ≫
      eqToHom (congrArg (fun q ↦ q.op ⋙ (A (s.obj t')).obj) (eg c))⟩
  have hmid (t : Under k) : m (𝟙 t) = 𝟙 (R t) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply Arrow.mk_injective _ _
    have h := congrArg Arrow.mk (NatTrans.congr_app (hid (s.obj t)) ((g t).op.obj U))
    dsimp only [m]
    simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, eqToHom_app]
    change Arrow.mk (_ ≫ eqToHom _) =
      Arrow.mk (𝟙 ((A (s.obj t)).obj.obj ((g t).op.obj U)))
    simp only [Arrow.arrow_mk_comp_eqToHom]
    rw [s.map_id]
    simpa only [NatTrans.comp_app, NatTrans.id_app, eqToHom_app,
      Arrow.arrow_mk_comp_eqToHom] using h
  have hmcomp {t t' t'' : Under k} (c : t ⟶ t') (d : t' ⟶ t'') :
      m (c ≫ d) = m c ≫ m d := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply Arrow.mk_injective _ _
    have ht := congrArg Arrow.mk
      (NatTrans.congr_app (hcomp (s.map c) (s.map d)) ((g t).op.obj U))
    have he : (f (s.map c)).op.obj ((g t).op.obj U) = (g t').op.obj U :=
      congrArg (fun q ↦ q.op.obj U) (eg c)
    dsimp only [m]
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app,
      Functor.whiskerLeft_app, eqToHom_app]
    simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    rw [arrow_transport_comp (θ (s.obj t') (s.obj t'') (s.map d)).hom he
      ((θ (s.obj t) (s.obj t') (s.map c)).hom.app ((g t).op.obj U))]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      ← Category.assoc, Arrow.arrow_mk_comp_eqToHom] at ht
    rw [← s.map_comp] at ht
    exact ht.symm
  let D : Under k ⥤ Sheaf (P j).toGrothendieck (Type u) :=
    { obj := R
      map := fun c ↦ m c
      map_id := hmid
      map_comp := hmcomp }
  let v (t : Under i) := (V.ι.app t.right).toFunctor
  let vj := (V.ι.app j).toFunctor
  have ev (t : Under k) : g t ⋙ v (s.obj t) = vj :=
    congrArg Cat.Hom.toFunctor (V.w (b ≫ t.hom))
  let z (t : Under i) : (A t).obj ⟶ (v t).op ⋙ colimit B :=
    β t ≫ Functor.whiskerLeft (v t).op (colimit.ι B t)
  let n (t : Under k) : (R t).obj ⟶ vj.op ⋙ colimit B :=
    Functor.whiskerLeft (g t).op (z (s.obj t)) ≫
      eqToHom (congrArg (fun q ↦ q.op ⋙ colimit B) (ev t))
  have hn {t t' : Under k} (c : t ⟶ t') : (m c).hom ≫ n t' = n t := by
    apply NatTrans.ext
    funext U
    apply Arrow.mk_injective _ _
    have he : (f (s.map c)).op.obj ((g t).op.obj U) = (g t').op.obj U :=
      congrArg (fun q ↦ q.op.obj U) (eg c)
    have hv : (v (s.obj t)).op.obj ((g t).op.obj U) =
        (v (s.obj t')).op.obj ((f (s.map c)).op.obj ((g t).op.obj U)) :=
      congrArg (fun q ↦ q.op.obj ((g t).op.obj U))
        (congrArg Cat.Hom.toFunctor (V.w c.right)).symm
    have h := arrow_postcomp (colimit.ι B (s.obj t')) hv _ _
      (hβmap (s.obj t) (s.obj t') (s.map c) ((g t).obj U.unop))
    have hw := NatTrans.congr_app (colimit.w B (s.map c))
      ((v (s.obj t)).op.obj ((g t).op.obj U))
    simp only [NatTrans.comp_app] at hw
    change Arrow.mk ((β (s.obj t)).app ((g t).op.obj U) ≫
      (B.map (s.map c)).app ((v (s.obj t)).op.obj ((g t).op.obj U)) ≫
        (colimit.ι B (s.obj t')).app ((v (s.obj t)).op.obj ((g t).op.obj U))) =
      Arrow.mk ((θ (s.obj t) (s.obj t') (s.map c)).hom.app ((g t).op.obj U) ≫
        (β (s.obj t')).app ((f (s.map c)).op.obj ((g t).op.obj U)) ≫
          (colimit.ι B (s.obj t')).app
            ((v (s.obj t')).op.obj ((f (s.map c)).op.obj ((g t).op.obj U)))) at h
    rw [hw] at h
    dsimp only [m, n]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    rw [arrow_transport_comp (z (s.obj t')) he
      ((θ (s.obj t) (s.obj t') (s.map c)).hom.app ((g t).op.obj U))]
    simpa only [z, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] using h.symm
  let ν : Cocone (D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)) :=
    { pt := vj.op ⋙ colimit B
      ι := { app := n, naturality := fun _ _ c ↦ hn c } }
  let e (t : Under k) :
      (D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)).obj t ≅
        (g t).op ⋙ (A (s.obj t)).obj := Iso.refl _
  have hD : ∀ (t t' : Under k) (c : t ⟶ t') (U : (F.obj j)ᵒᵖ),
      Arrow.mk (((D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)).map c).app U ≫
        (e t').hom.app U) =
      Arrow.mk ((e t).hom.app U ≫
        (θ (s.obj t) (s.obj t') (s.map c)).hom.app ((g t).op.obj U)) := by
    intro t t' c U
    simp only [e, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
    change Arrow.mk ((m c).hom.app U) = _
    dsimp only [m]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      Arrow.arrow_mk_comp_eqToHom]
  have hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫ (β (s.obj t)).app ((g t).op.obj U) ≫
        (colimit.ι B (s.obj t)).app ((v (s.obj t)).op.obj ((g t).op.obj U))) := by
    intro t U
    simp only [ν, n, z, e, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
      ← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
  obtain ⟨hνcolim⟩ := colimit_stage_kan_cocone J F V hobjects harrows i
    (fun t ↦ (A t).obj) (fun t t' c ↦ (θ t t' c).hom)
    (fun t X ↦ by
      simpa only [NatTrans.comp_app, eqToHom_app, NatTrans.id_app,
        Arrow.arrow_mk_comp_eqToHom] using
        congrArg Arrow.mk (NatTrans.congr_app (hid t) X))
    (fun t t' t'' c d X ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
        ← Category.assoc, Arrow.arrow_mk_comp_eqToHom] using
        congrArg Arrow.mk (NatTrans.congr_app (hcomp c d) X))
    B β hβ hβmap j k a b
    (D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)) e hD
    ν rfl hν
  refine ⟨k, a, b, D, ⟨(colimit.isColimit _).coconePointUniqueUpToIso hνcolim⟩, ?_⟩
  intro t
  exact ⟨Iso.refl _⟩

end CategoryTheory
