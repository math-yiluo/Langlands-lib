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
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteAbelianKanUnitRelations

/-! # Raw abelian section relations

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section presentation; Modules on Sites, Tag 03CO (abelian colimits).
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_postcomp_app {C : Type u} [Category C]
    (A B : C ⥤ AddCommGrpCat.{u}) (α : A ⟶ B) {p q : C} (e : p = q)
    {X : AddCommGrpCat.{u}} (f : X ⟶ A.obj p) (g : X ⟶ A.obj q)
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (f ≫ α.app p) = Arrow.mk (g ≫ α.app q) := by
  subst q
  rw [Arrow.mk_injective _ _ h]

private theorem arrow_precomp {X Y Z Z' : AddCommGrpCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (g' : Y ⟶ Z')
    (h : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f ≫ g') := by
  obtain ⟨hX, hZ, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst Z'
  simpa using congrArg (fun k ↦ Arrow.mk (f ≫ k)) hg

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section presentation; Modules on Sites, Tag 03CO (abelian colimits).
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-relations).

Proof: Normalize the two section images to Y = V_i(U) using the equalities in
hkappa. The equations hbeta_map and hm make these normalized maps compatible
with D and B. Evaluation and the abelian forgetful functor preserve filtered
colimits; their eventual equality criterion moves both images to a common stage
k, where cancellation of the endpoint transport yields equality of beta_k unit
images. In the abelian pointwise Kan colimit, their difference is a finite sum
of defining relations: additivity within one group and restriction along a
stage arrow. Lift all endpoints, arrows and defining triangles for this finite
sum to a further common stage in Under i. Eventual object and arrow equality
make each lifted triangle commute. Naturality of theta makes each restriction
relation vanish after restriction to the forward image of U; additivity makes
the linear relations vanish. Thus the two transported sections agree there.
The equation hm and injectivity of E identify the two D images. Compose the
refinement arrows with those to k to get the displayed eventual equality.
This proves identification of representatives only, not their existence.
-/
theorem raw_abelian_section_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (U : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom))
    (κ : ∀ t : Under i,
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)))
    (hκ : ∀ t : Under i,
        ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
            (V.ι.app i).toFunctor.obj U,
          κ t =
            (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
              (colimit.ι B t).app
                (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
              eqToHom (congrArg (fun X => (colimit B).obj (op X)) e)) :
    ∀ (t t' : Under i) (x : D.obj t) (x' : D.obj t'),
      κ t x = κ t' x' →
        ∃ (r : Under i) (b : t ⟶ r) (b' : t' ⟶ r), D.map b x = D.map b' x' := by
  classical
  choose e he using hκ
  let Y := (V.ι.app i).toFunctor.obj U
  let f : ∀ t : Under i, D.obj t ⟶ (B.obj t).obj (op Y) := fun t ↦
    (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
      eqToHom (congrArg (fun X ↦ (B.obj t).obj (op X)) (e t))
  have hf : ∀ (t t' : Under i) (b : t ⟶ t'),
      f t ≫ (B.map b).app (op Y) = D.map b ≫ f t' := by
    intro t t' b
    have hu : (F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (F.map t'.hom).toFunctor.obj U := by
      rw [← Cat.Hom.comp_obj, ← F.map_comp, Under.w b]
    have h₁ := arrow_precomp (E t).hom _ _
      (hβmap t t' b ((F.map t.hom).toFunctor.obj U))
    have h₂ := arrow_postcomp_app
      (((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj)
      ((V.ι.app t'.right).toFunctor.op ⋙ B.obj t') (β t') (congrArg op hu)
      _ _ (hm t t' b)
    have hn := (B.map b).naturality (eqToHom (congrArg op (e t)))
    simp only [eqToHom_map] at hn
    apply Arrow.mk_injective _ _
    calc
      Arrow.mk (f t ≫ (B.map b).app (op Y)) =
          Arrow.mk ((E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
            (B.map b).app
              (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U)))) := by
        dsimp [f, Y]
        simp only [Category.assoc]
        rw [hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk (D.map b ≫ (E t').hom ≫
          (β t').app (op ((F.map t'.hom).toFunctor.obj U))) := by
        simpa only [Category.assoc] using h₁.trans h₂
      _ = Arrow.mk (D.map b ≫ f t') := by
        dsimp [f]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  have hk : ∀ t : Under i, κ t = f t ≫ (colimit.ι B t).app (op Y) := by
    intro t
    rw [he t]
    have hn := (colimit.ι B t).naturality (eqToHom (congrArg op (e t)))
    simp only [eqToHom_map] at hn
    dsimp [f, Y]
    simp only [Category.assoc]
    rw [hn]
  intro t t' x x' h
  let ev := (evaluation V.ptᵒᵖ AddCommGrpCat.{u}).obj (op Y) ⋙ forget AddCommGrpCat
  have hc := isColimitOfPreserves ev (colimit.isColimit B)
  have hh : (ev.mapCocone (colimit.cocone B)).ι.app t (f t x) =
      (ev.mapCocone (colimit.cocone B)).ι.app t' (f t' x') := by
    rw [hk t, hk t'] at h
    change (colimit.ι B t).app (op Y) (f t x) =
      (colimit.ι B t').app (op Y) (f t' x')
    exact h
  obtain ⟨k, b, b', hb⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (B ⋙ ev) hc).mp hh
  have hb₁ := ConcreteCategory.congr_hom (hf t k b) x
  have hb₂ := ConcreteCategory.congr_hom (hf t' k b') x'
  have hfk : f k (D.map b x) = f k (D.map b' x') := by
    exact hb₁.symm.trans (hb.trans hb₂)
  have hβk : (β k).app (op ((F.map k.hom).toFunctor.obj U))
      ((E k).hom (D.map b x)) =
      (β k).app (op ((F.map k.hom).toFunctor.obj U))
        ((E k).hom (D.map b' x')) := by
    exact (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (fun X ↦ (B.obj k).obj (op X)) (e k)))).1 hfk
  obtain ⟨r, c, hc⟩ := raw_abelian_section_kan_unit_relations
    J F V hobjects harrows i k
      (fun r ↦ ((sheafPullback (F.map r.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P r.right).toGrothendieck).obj G).obj)
      (fun r c ↦ (θ k r c).hom) (B.obj k) (β k) (hβ k)
      ((F.map k.hom).toFunctor.obj U)
      ((E k).hom (D.map b x)) ((E k).hom (D.map b' x')) hβk
  refine ⟨r, b ≫ c, b' ≫ c, ?_⟩
  have hm' := (Arrow.mk_eq_mk_iff _ _).mp (hm k r c)
  obtain ⟨_, er, hm'⟩ := hm'
  have hx := ConcreteCategory.congr_hom hm' (D.map b x)
  have hx' := ConcreteCategory.congr_hom hm' (D.map b' x')
  have hd : D.map c (D.map b x) = D.map c (D.map b' x') := by
    apply (ConcreteCategory.bijective_of_isIso (E r).hom).1
    apply (ConcreteCategory.bijective_of_isIso (eqToHom er.symm)).1
    simpa only [AddCommGrpCat.comp_apply, eqToHom_refl, AddCommGrpCat.id_apply] using
      hx.symm.trans (hc.trans hx')
  simpa only [D.map_comp, AddCommGrpCat.comp_apply] using hd


end CategoryTheory
