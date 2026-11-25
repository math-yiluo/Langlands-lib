/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Coherent diagrams of abelian inverse-image sections

Source: Stacks Project, Sites, Tag 0A35, the compatible stage-map construction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem sheaf_unit_unique
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous T S]
    (G : Sheaf T AddCommGrpCat.{u}) (H : Sheaf S AddCommGrpCat.{u})
    (a b : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶ H)
    (h : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ b.hom.app (op (f.obj X)))) : a = b := by
  apply ((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).homEquiv G H).injective
  ext1
  apply NatTrans.ext
  funext X
  exact (Arrow.mk_inj _ _).mp (h (unop X))

private theorem sheaf_triangle_comp
    {C D E Z : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [SmallCategory Z]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (Q : GrothendieckTopology Z)
    (f : C ⥤ D) (g : D ⥤ E) (k : E ⥤ Z)
    (h : C ⥤ E) (l : C ⥤ Z) (m : D ⥤ Z)
    [f.IsContinuous T S] [g.IsContinuous S R] [k.IsContinuous R Q]
    [h.IsContinuous T R] [l.IsContinuous T Q] [m.IsContinuous S Q]
    (w₁ : f ⋙ g = h) (w₂ : h ⋙ k = l) (w₃ : g ⋙ k = m)
    (G : Sheaf T AddCommGrpCat.{u})
    (a : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
        ((sheafPullback h AddCommGrpCat.{u} T R).obj G))
    (b : (sheafPullback h AddCommGrpCat.{u} T R).obj G ⟶
      (k.sheafPushforwardContinuous AddCommGrpCat.{u} R Q).obj
        ((sheafPullback l AddCommGrpCat.{u} T Q).obj G))
    (c : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (m.sheafPushforwardContinuous AddCommGrpCat.{u} S Q).obj
        ((sheafPullback l AddCommGrpCat.{u} T Q).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
        (op X)))
    (hb : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
        (op X) ≫ b.hom.app (op (h.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l AddCommGrpCat.{u} T Q).unit.app G).hom.app
        (op X)))
    (hc : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ c.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l AddCommGrpCat.{u} T Q).unit.app G).hom.app
        (op X))) (Y : D) :
    Arrow.mk (a.hom.app (op Y) ≫ b.hom.app (op (g.obj Y))) =
      Arrow.mk (c.hom.app (op Y)) := by
  subst h
  subst l
  subst m
  have eq : a ≫ (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).map b = c := by
    apply sheaf_unit_unique T S f G _
    intro X
    change Arrow.mk
      (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app (op X) ≫
        (a.hom.app (op (f.obj X)) ≫ b.hom.app (op (g.obj (f.obj X))))) = _
    rw [← Category.assoc, (Arrow.mk_inj _ _).mp (ha X)]
    exact (hb X).trans (hc X).symm
  exact congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq

private theorem sheaf_triangle_id
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (f : C ⥤ D) (g : D ⥤ D)
    [f.IsContinuous T S] [g.IsContinuous S S]
    (w : g = 𝟭 D) (G : Sheaf T AddCommGrpCat.{u})
    (a : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S S).obj
        ((sheafPullback f AddCommGrpCat.{u} T S).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X))) (Y : D) :
    Arrow.mk (a.hom.app (op Y)) =
      Arrow.mk (𝟙 (((sheafPullback f AddCommGrpCat.{u} T S).obj G).obj.obj (op Y))) := by
  subst g
  let b : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      ((𝟭 D).sheafPushforwardContinuous AddCommGrpCat.{u} S S).obj
        ((sheafPullback f AddCommGrpCat.{u} T S).obj G) := ⟨𝟙 _⟩
  have eq : a = b := by
    apply sheaf_unit_unique T S f G _
    intro X
    change Arrow.mk (_ ≫ a.hom.app (op (f.obj X))) = Arrow.mk (_ ≫ 𝟙 _)
    rw [Category.comp_id]
    exact ha X
  simpa [b] using congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq

/-- Source: Stacks Project, Sites, Tag 0A35, the compatible stage maps in the
adjunction paragraph (expanded using uniqueness of adjuncts).
(blueprint: lem-weil-pbc-colimit-site-abelian-section-diagram).

Proof: Evaluate the inverse image along t.hom at its image of U. For b : t ⟶ t',
map sections by θ b and transport the target along F.map_comp and Under.w b.
Choose these evaluations as D's objects and the identity component isomorphisms E.
The unit equations determine each θ uniquely: transpose back through the stage
adjunction and use equality of all presheaf components. This proves identity and
composition, so D is a functor. Use the evaluation of the limit inverse image as
K.pt and the components of α as K's legs, transported along cocone naturality.
Transposing θ b followed by the restriction of α t' shows that it equals α t:
both transpose to the limit unit. Evaluating gives K's naturality. Take e to be
the identity. The asserted arrow equalities are the definitions of the legs and
transition maps, with endpoint transports recorded. This argument uses neither
filteredness nor a colimit hypothesis. Empty source categories have no U and
empty indexing categories have no i; no group is chosen from mere existence.
-/
theorem colimit_site_abelian_section_diagram
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F) (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i) :
    ∃ (D : Under i ⥤ AddCommGrpCat.{u})
      (E : ∀ t : Under i, D.obj t ≅
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G).obj.obj (op ((F.map t.hom).toFunctor.obj U))) (K : Cocone
        D) (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U))),
      (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧ (∀ (t t' :
        Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫ (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) := by
  classical
  let L (t : Under i) :=
    (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let W (t : Under i) (X : F.obj i) := (F.map t.hom).toFunctor.obj X
  have w {t t' : Under i} (b : t ⟶ t') :
      (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map t'.hom).toFunctor := by
    change (F.map t.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  have hw {t t' : Under i} (b : t ⟶ t') (X : F.obj i) :
      (F.map b.right).toFunctor.obj (W t X) = W t' X :=
    congrArg (fun f ↦ f.obj X) (w b)
  have hv (t : Under i) :
      (F.map t.hom).toFunctor ⋙ (V.ι.app t.right).toFunctor =
        (V.ι.app i).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w t.hom)
  have hvo (t : Under i) (X : F.obj i) :
      (V.ι.app t.right).toFunctor.obj (W t X) = (V.ι.app i).toFunctor.obj X :=
    congrArg (fun f ↦ f.obj X) (hv t)
  have hid (t : Under i) (Y : F.obj t.right) :
      Arrow.mk ((θ t t (𝟙 t)).hom.app (op Y)) = Arrow.mk (𝟙 ((L t).obj.obj (op Y))) := by
    exact sheaf_triangle_id (P i).toGrothendieck (P t.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map (Under.Hom.right (𝟙 t))).toFunctor
      (by change (F.map (𝟙 t.right)).toFunctor = _; simp) G (θ t t (𝟙 t))
      (hθ t t (𝟙 t)) Y
  have hcomp (t t' t'' : Under i) (b : t ⟶ t') (c : t' ⟶ t'')
      (Y : F.obj t.right) :
      Arrow.mk ((θ t t' b).hom.app (op Y) ≫
        (θ t' t'' c).hom.app (op ((F.map b.right).toFunctor.obj Y))) =
      Arrow.mk ((θ t t'' (b ≫ c)).hom.app (op Y)) := by
    apply sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck (P t''.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map c.right).toFunctor
      (F.map t'.hom).toFunctor (F.map t''.hom).toFunctor
      (F.map (b ≫ c).right).toFunctor (w b) (w c) _ G
      (θ t t' b) (θ t' t'' c) (θ t t'' (b ≫ c))
      (hθ t t' b) (hθ t' t'' c) (hθ t t'' (b ≫ c)) Y
    change (F.map b.right ≫ F.map c.right).toFunctor = _
    rw [← F.map_comp]
    rfl
  have hcone (t t' : Under i) (b : t ⟶ t') (Y : F.obj t.right) :
      Arrow.mk ((θ t t' b).hom.app (op Y) ≫
        (α t').hom.app (op ((F.map b.right).toFunctor.obj Y))) =
      Arrow.mk ((α t).hom.app (op Y)) := by
    exact sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (V.ι.app t'.right).toFunctor
      (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
      (w b) (hv t') (congrArg Cat.Hom.toFunctor (V.w b.right)) G
      (θ t t' b) (α t') (α t) (hθ t t' b) (hα t') (hα t) Y
  let A (t : Under i) := (L t).obj.obj (op (W t U))
  let m {t t' : Under i} (b : t ⟶ t') : A t ⟶ A t' :=
    (θ t t' b).hom.app (op (W t U)) ≫
      eqToHom (congrArg (fun Y ↦ (L t').obj.obj (op Y)) (hw b U))
  have hm_id (t : Under i) : m (𝟙 t) = 𝟙 (A t) := by
    apply (Arrow.mk_injective _ _)
    simpa only [m, Arrow.arrow_mk_comp_eqToHom] using hid t (W t U)
  have hm_comp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      m (b ≫ c) = m b ≫ m c := by
    apply (Arrow.mk_injective _ _)
    have hn := (θ t' t'' c).hom.naturality (eqToHom (congrArg op (hw b U)))
    simp only [eqToHom_map] at hn
    calc
      Arrow.mk (m (b ≫ c)) = Arrow.mk ((θ t t'' (b ≫ c)).hom.app (op (W t U))) := by
        simp only [m, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk ((θ t t' b).hom.app (op (W t U)) ≫
          (θ t' t'' c).hom.app (op ((F.map b.right).toFunctor.obj (W t U)))) :=
        (hcomp t t' t'' b c (W t U)).symm
      _ = Arrow.mk (m b ≫ m c) := by
        dsimp only [m]
        rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  let D : Under i ⥤ AddCommGrpCat.{u} :=
    { obj := A
      map := fun b ↦ m b
      map_id := hm_id
      map_comp := fun b c ↦ hm_comp b c }
  let H := (sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let k (t : Under i) : A t ⟶ H.obj.obj (op ((V.ι.app i).toFunctor.obj U)) :=
    (α t).hom.app (op (W t U)) ≫
      eqToHom (congrArg (fun Y ↦ H.obj.obj (op Y)) (hvo t U))
  have hk {t t' : Under i} (b : t ⟶ t') : m b ≫ k t' = k t := by
    apply (Arrow.mk_injective _ _)
    have hn := (α t').hom.naturality (eqToHom (congrArg op (hw b U)))
    simp only [eqToHom_map] at hn
    calc
      Arrow.mk (m b ≫ k t') =
          Arrow.mk ((θ t t' b).hom.app (op (W t U)) ≫
            (α t').hom.app (op ((F.map b.right).toFunctor.obj (W t U)))) := by
        dsimp only [m, k]
        rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk ((α t).hom.app (op (W t U))) := hcone t t' b (W t U)
      _ = Arrow.mk (k t) := by simp only [k, Arrow.arrow_mk_comp_eqToHom]
  let K : Cocone D :=
    { pt := H.obj.obj (op ((V.ι.app i).toFunctor.obj U))
      ι :=
        { app := k
          naturality := fun _ _ b ↦ by
            change m b ≫ k _ = k _ ≫ 𝟙 _
            rw [Category.comp_id]
            exact hk b } }
  refine ⟨D, (fun t ↦ Iso.refl (A t)), K, Iso.refl _, ?_, ?_⟩
  · intro t
    change Arrow.mk (k t ≫ 𝟙 _) = Arrow.mk (𝟙 _ ≫ (α t).hom.app (op (W t U)))
    simp only [Category.comp_id, Category.id_comp, k, Arrow.arrow_mk_comp_eqToHom]
  · intro t t' b
    change Arrow.mk (𝟙 _ ≫ (θ t t' b).hom.app (op (W t U))) = Arrow.mk (m b ≫ 𝟙 _)
    simp only [Category.comp_id, Category.id_comp, m, Arrow.arrow_mk_comp_eqToHom]

end CategoryTheory
