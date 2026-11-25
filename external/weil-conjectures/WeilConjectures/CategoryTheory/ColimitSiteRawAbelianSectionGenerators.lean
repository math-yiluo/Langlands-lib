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
import all WeilConjectures.CategoryTheory.ColimitSiteRawSectionGenerators
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # Raw abelian section generators

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section presentation; Modules on Sites, Tag 03CO (abelian colimits).
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-generators).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem colimit_mem_subgroup {I : Type u} [SmallCategory I]
    (D : I ⥤ AddCommGrpCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (S : AddSubgroup c.pt) (hS : ∀ i x, c.ι.app i x ∈ S) (x : c.pt) : x ∈ S := by
  let c' : Cocone D :=
    { pt := AddCommGrpCat.of S
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom ((c.ι.app i).hom.codRestrict S (hS i))
          naturality := fun i j f ↦ by
            apply AddCommGrpCat.hom_ext
            ext x
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (c.ι.naturality f) x } }
  let inc : c'.pt ⟶ c.pt := AddCommGrpCat.ofHom S.subtype
  have he : hc.desc c' ≫ inc = 𝟙 c.pt := by
    apply hc.hom_ext
    intro i
    rw [← Category.assoc, hc.fac]
    rfl
  have hx := ConcreteCategory.congr_hom he x
  change ((hc.desc c' x : S) : c.pt) = x at hx
  exact hx ▸ (hc.desc c' x).property

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section presentation; Modules on Sites, Tag 03CO (abelian colimits).
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-generators).

Proof: First lift one pointwise Kan generator (W, s, f : Y → V_t(W)), where
Y = V_i(U). The object and arrow set-colimit hypotheses lift f with its prescribed
endpoints at a common stage receiving i and t.right. Equalize the two arrows out
of i to obtain b in Under i. Apply theta_b to s, restrict along the lifted arrow,
and apply E inverse. Naturality of beta and hbeta_map identify this section's
kappa image with the outer image of the original Kan generator.

Let S be the union of the ranges of kappa. It is an additive subgroup: zero and
negatives come from one stage, and a sum comes from a common upper stage by
hkappa_map and additivity of D. For fixed t, take the preimage of S under the
evaluated coprojection B_t(Y) → (colimit B)(Y). Every pointwise Kan generator
lies in that subgroup by the preceding lift. A subgroup of an abelian colimit
containing all coprojection images is the whole group: corestrict the cocone
legs to the subgroup, use the colimit universal property to descend to it,
and compose with the inclusion. Colimit hom_ext makes the composite the
identity. The private proved lemma colimit_mem_subgroup formalizes this fact.
Apply it to the pointwise Kan cocone. Finally, evaluation and the abelian
forgetful functor preserve the outer filtered colimit, so every outer section
comes from some B_t(Y) and therefore belongs to S. This argument includes the
empty sum and proves representative existence without any relation criterion.
-/
theorem raw_abelian_section_generators
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
    (κ : ∀ t : Under i,
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)))
    (hκmap : ∀ (t t' : Under i) (b : t ⟶ t'), D.map b ≫ κ t' = κ t)
    (hκ : ∀ t : Under i,
        ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
            (V.ι.app i).toFunctor.obj U,
          κ t =
            (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
              (colimit.ι B t).app
                (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
              eqToHom (congrArg (fun X => (colimit B).obj (op X)) e)) :
    ∀ x : (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)),
      ∃ (t : Under i) (y : D.obj t), κ t y = x := by
  classical
  let Y := (V.ι.app i).toFunctor.obj U
  let H := colimit B
  have hsingle (t : Under i) (W : F.obj t.right)
      (f : op ((V.ι.app t.right).toFunctor.obj W) ⟶ op Y)
      (s : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op W)) :
      ∃ (t' : Under i) (y : D.obj t'), κ t' y =
        (colimit.ι B t).app (op Y) ((B.obj t).map f ((β t).app (op W) s)) := by
    obtain ⟨t', b, g, hg⟩ := lift_under_arrow F V hobjects harrows t U W f.unop
    let δ (t : Under i) := β t ≫
      Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
    let y := (E t').inv
      (((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op
          ((θ t t' b).hom.app (op W) s))
    refine ⟨t', y, ?_⟩
    obtain ⟨e, he⟩ := hκ t'
    have hV : (V.ι.app t.right).toFunctor.obj W =
        (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj W) :=
      (congrArg (fun f : F.obj t.right ⟶ V.pt ↦ f.toFunctor.obj W)
        (V.w b.right)).symm
    have hd : Arrow.mk ((δ t).app (op W)) =
        Arrow.mk ((θ t t' b).hom.app (op W) ≫
          (δ t').app (op ((F.map b.right).toFunctor.obj W))) := by
      have htransport : ∀ {Y Z : V.ptᵒᵖ} (e : Y = Z)
          (f : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op W) ⟶
            (B.obj t').obj Y)
          (g : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op W) ⟶
            (B.obj t').obj Z),
          Arrow.mk f = Arrow.mk g →
            Arrow.mk (f ≫ (colimit.ι B t').app Y) =
              Arrow.mk (g ≫ (colimit.ι B t').app Z) := by
        intro Y Z e f g h
        subst Z
        rw [Arrow.mk_injective _ _ h]
      have hh := htransport (congrArg op hV) _ _ (hβmap t t' b W)
      dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
      change Arrow.mk ((β t).app (op W) ≫ _) = _
      calc
        _ = Arrow.mk ((β t).app (op W) ≫ (B.map b).app (op
            ((V.ι.app t.right).toFunctor.obj W)) ≫
            (colimit.ι B t').app (op ((V.ι.app t.right).toFunctor.obj W))) := by
          congr 1
          simp only [Functor.op_obj, ← NatTrans.comp_app, colimit.w]
        _ = _ := by simpa only [δ, NatTrans.comp_app, Functor.whiskerLeft_app,
          Category.assoc, Functor.op_obj] using hh
    have hmap : Arrow.mk (H.map f) =
        Arrow.mk (H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
      exact congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.map a.hom.op)) hg.symm
    have hcomp : Arrow.mk ((δ t).app (op W) ≫ H.map f) =
        Arrow.mk (((θ t t' b).hom.app (op W) ≫
          (δ t').app (op ((F.map b.right).toFunctor.obj W))) ≫
            H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
      obtain ⟨hA, hB, hd⟩ := (Arrow.mk_eq_mk_iff _ _).mp hd
      obtain ⟨hB', hC, hmap⟩ := (Arrow.mk_eq_mk_iff _ _).mp hmap
      apply (Arrow.mk_eq_mk_iff _ _).mpr
      refine ⟨rfl, hC, ?_⟩
      simp [hd, hmap, Category.assoc]
    have hn := (δ t').naturality g.op
    change _ = (δ t').app (op ((F.map b.right).toFunctor.obj W)) ≫
      H.map ((V.ι.app t'.right).toFunctor.map g).op at hn
    have heq : (δ t).app (op W) ≫ H.map f =
        (θ t t' b).hom.app (op W) ≫
          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op ≫
            (δ t').app (op ((F.map t'.hom).toFunctor.obj U)) ≫
              eqToHom (congrArg (fun X ↦ H.obj (op X)) e) := by
      apply Arrow.mk_injective
      simpa only [Category.assoc, hn, ← Category.assoc,
        Arrow.arrow_mk_comp_eqToHom] using hcomp
    have hy : (E t').hom y =
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op
            ((θ t t' b).hom.app (op W) s) := by
      exact ConcreteCategory.congr_hom (E t').inv_hom_id _
    rw [he]
    change (eqToHom (congrArg (fun X ↦ H.obj (op X)) e))
      ((δ t').app (op ((F.map t'.hom).toFunctor.obj U)) ((E t').hom y)) =
        (colimit.ι B t).app (op Y) ((B.obj t).map f ((β t).app (op W) s))
    rw [hy]
    have hnat := ConcreteCategory.congr_hom ((colimit.ι B t).naturality f).symm
      ((β t).app (op W) s)
    change H.map f ((δ t).app (op W) s) = (colimit.ι B t).app (op Y)
      ((B.obj t).map f ((β t).app (op W) s)) at hnat
    exact (ConcreteCategory.congr_hom heq s).symm.trans hnat
  let S : AddSubgroup (H.obj (op Y)) :=
    { carrier := {x | ∃ t y, κ t y = x}
      zero_mem' := ⟨Under.mk (𝟙 i), 0, map_zero _⟩
      add_mem' := by
        rintro x y ⟨t, x', rfl⟩ ⟨t', y', rfl⟩
        let r := IsFiltered.max t t'
        let b : t ⟶ r := IsFiltered.leftToMax t t'
        let c : t' ⟶ r := IsFiltered.rightToMax t t'
        refine ⟨r, D.map b x' + D.map c y', ?_⟩
        rw [map_add]
        exact congrArg₂ (fun a b ↦ a + b)
          (ConcreteCategory.congr_hom (hκmap t r b) x')
          (ConcreteCategory.congr_hom (hκmap t' r c) y')
      neg_mem' := by
        rintro x ⟨t, y, rfl⟩
        exact ⟨t, -y, map_neg _ _⟩ }
  intro x
  let ev := (evaluation V.ptᵒᵖ AddCommGrpCat.{u}).obj (op Y)
  obtain ⟨t, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (ev ⋙ forget AddCommGrpCat) (colimit.isColimit B)) x
  change (colimit.ι B t).app (op Y) z = x at hz
  rw [← hz]
  change (colimit.ι B t).app (op Y) z ∈ S
  let St := S.comap ((colimit.ι B t).app (op Y)).hom
  have : (B.obj t).IsLeftKanExtension (β t) := hβ t
  let c := (Functor.LeftExtension.mk _ (β t)).coconeAt (op Y)
  have hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (B.obj t) (β t) (op Y)
  exact colimit_mem_subgroup _ c hc St (fun a s ↦ hsingle t a.left.unop a.hom s) z


end CategoryTheory
