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
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianSectionGenerators
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianSectionRelations

/-! # ColimitSiteRawAbelianSectionEvaluation

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs; abelian colimits
as in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-evaluation).

Proof: Construct R as the chosen abelian colimit cocone of D. Put Y = V_i(U).
For each t the cocone equation gives e_t : V_t(F(t.hom)(U)) = Y. Compose E_t,
the component of β_t, the coprojection into colimit B and the transport along
e_t. The equations hm and hβmap and naturality of the coprojections prove that
these maps are a cocone. Hence they induce μ : R.pt → (colimit B)(Y).

Construct an inverse by the pointwise Kan formula. An abelian Kan generator is
(W, x, f : Y → V_t(W)). Lift f and both endpoints to a stage receiving i and
t.right using the object and arrow set-colimit hypotheses. Refine further to
align the endpoints with the prescribed images, and equalize the arrows out
of i so the refinement is an arrow b : t → t' in Under i. Apply θ_b to x,
restrict along the lifted f, apply E_t' inverse, and take the coprojection of D.
Extend this map additively to finite sums of generators. Two choices of stage,
endpoint or arrow lifts agree at a further common refinement by eventual
object and arrow equality; naturality of θ and hm then give the same D class.
Linearity relations are respected by additivity. For a Kan restriction relation
lift its defining triangle to one stage and use presheaf naturality. Transition
relations are respected by hβmap and hm. Every relation in the abelian colimit
is a finite sum of these relations, so filteredness supplies one common stage.
The additive assignment therefore descends to an inverse ψ of μ.

On a D generator choose its own stage and the identity restriction: ψμ is the
identity by the defining section maps. On a Kan generator the lifted restriction
is a Kan relation, so naturality of β and hβmap prove μψ is the identity. Thus
q is the isomorphism with hom μ; no arbitrary witness is used for R or q.
Compose the coprojection formula for q with colimit.desc B γ. Naturality moves
the endpoint transport to T, colimit.ι_desc_app replaces the coprojection by γ_t,
and ha replaces β_t followed by γ_t by a_t. Arrow equality removes the endpoint
transport and yields the stated formula. No finiteness of covers, sheaf condition
on T or colimit B, or equality in the canonical inverse image is assumed.
-/
theorem colimit_site_raw_abelian_section_evaluation
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
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
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
    (T : V.ptᵒᵖ ⥤ AddCommGrpCat.{u})
    (γ : B ⟶ (Functor.const (Under i)).obj T)
    (a : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ T)
    (ha : ∀ (t : Under i) (X : F.obj t.right),
      (β t).app (op X) ≫
        (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj X)) = (a t).app (op X))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∃ (R : Cocone D)
      (q : R.pt ≅ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))),
      Nonempty (IsColimit R) ∧
      ∀ t : Under i,
        Arrow.mk (R.ι.app t ≫ q.hom ≫
          (colimit.desc B (Cocone.mk T γ)).app
            (op ((V.ι.app i).toFunctor.obj U))) =
        Arrow.mk ((E t).hom ≫ (a t).app (op ((F.map t.hom).toFunctor.obj U))) := by
  have _ := hθ
  have hpre : ∀ {A B C D : AddCommGrpCat.{u}} (f : A ⟶ B) (g : A ⟶ C),
      Arrow.mk f = Arrow.mk g → (k : D ⟶ A) →
        Arrow.mk (k ≫ f) = Arrow.mk (k ≫ g) := by
    intro A B C D f g h k
    obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff f g).mp h
    apply (Arrow.mk_eq_mk_iff _ _).mpr
    refine ⟨rfl, hB, ?_⟩
    simp [hf, Category.assoc]
  have hpost : ∀ {C : Type u} [SmallCategory C]
      {S T : C ⥤ AddCommGrpCat.{u}} (δ : S ⟶ T) {A : AddCommGrpCat.{u}} {Y Z : C},
      Y = Z → (f : A ⟶ S.obj Y) → (g : A ⟶ S.obj Z) →
      Arrow.mk f = Arrow.mk g →
      Arrow.mk (f ≫ δ.app Y) = Arrow.mk (g ≫ δ.app Z) := by
    intro C _ S T δ A Y Z e f g h
    subst Z
    rw [Arrow.mk_injective _ _ h]
  let e (t : Under i) :
      (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (V.ι.app i).toFunctor.obj U :=
    congrArg (fun f : F.obj i ⟶ V.pt ↦ f.toFunctor.obj U) (V.w t.hom)
  let κ (t : Under i) :
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)) :=
    (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
      (colimit.ι B t).app
        (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
      eqToHom (congrArg (fun X ↦ (colimit B).obj (op X)) (e t))
  have hκ {t t' : Under i} (b : t ⟶ t') : D.map b ≫ κ t' = κ t := by
    have hU : (F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (F.map t'.hom).toFunctor.obj U := by
      change (F.map t.hom ≫ F.map b.right).toFunctor.obj U = _
      rw [← F.map_comp, Under.w b]
    have hV : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (V.ι.app t'.right).toFunctor.obj
          ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U)) := by
      exact (congrArg (fun f : F.obj t.right ⟶ V.pt ↦
        f.toFunctor.obj ((F.map t.hom).toFunctor.obj U)) (V.w b.right)).symm
    have h₁ := hpre _ _ (hβmap t t' b ((F.map t.hom).toFunctor.obj U))
      (E t).hom
    have h₂ := hpost (colimit.ι B t') (congrArg op hV) _ _ h₁
    have h₃ := hpost (β t') (congrArg op hU) _ _ (hm t t' b)
    have h₄ := hpost (colimit.ι B t')
      (congrArg (fun X ↦ op ((V.ι.app t'.right).toFunctor.obj X)) hU) _ _ h₃
    apply Arrow.mk_injective
    simp only [κ, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    calc
      _ = Arrow.mk (((E t).hom ≫
          (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (β t').app (op ((F.map b.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) ≫
          (colimit.ι B t').app (op ((V.ι.app t'.right).toFunctor.obj
            ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))))) := by
        simpa only [Category.assoc] using h₄.symm
      _ = Arrow.mk (((E t).hom ≫
          (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (B.map b).app (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) ≫
          (colimit.ι B t').app (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) := by
        simpa only [Category.assoc] using h₂.symm
      _ = _ := by
        congr 1
        simp only [Category.assoc, ← NatTrans.comp_app, colimit.w]
  let K : Cocone D :=
    { pt := (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))
      ι := { app := κ, naturality := fun _ _ b ↦ by simpa using hκ b } }
  have hformula : ∀ t : Under i,
      ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
          (V.ι.app i).toFunctor.obj U,
        κ t = (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (colimit.ι B t).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
          eqToHom (congrArg (fun X ↦ (colimit B).obj (op X)) e) :=
    fun t ↦ ⟨e t, rfl⟩
  have hgen := raw_abelian_section_generators
    J F P V hobjects harrows i G θ B β hβ hβmap U D E κ (fun _ _ b ↦ hκ b) hformula
  have hrel := raw_abelian_section_relations
    J F P V hobjects harrows i G θ B β hβ hβmap U D E hm κ hformula
  let R : Cocone D := colimit.cocone D
  let μ : R.pt ⟶ K.pt := colimit.desc D K
  have hμ (t : Under i) : R.ι.app t ≫ μ = κ t := colimit.ι_desc K t
  have hc := isColimitOfPreserves (forget AddCommGrpCat) (colimit.isColimit D)
  have hsurj : Function.Surjective μ := by
    intro x
    obtain ⟨t, y, hy⟩ := hgen x
    refine ⟨R.ι.app t y, ?_⟩
    exact (ConcreteCategory.congr_hom (hμ t) y).trans hy
  have hinj : Function.Injective μ := by
    intro x y h
    obtain ⟨t, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    obtain ⟨t', y', hy⟩ := Types.jointly_surjective_of_isColimit hc y
    change R.ι.app t x' = x at hx
    change R.ι.app t' y' = y at hy
    have hh : κ t x' = κ t' y' := by
      rw [← ConcreteCategory.congr_hom (hμ t) x',
        ← ConcreteCategory.congr_hom (hμ t') y']
      change μ (R.ι.app t x') = μ (R.ι.app t' y')
      rwa [hx, hy]
    obtain ⟨r, b, c, he⟩ := hrel t t' x' y' hh
    have hb := ConcreteCategory.congr_hom (R.ι.naturality b) x'
    have hc' := ConcreteCategory.congr_hom (R.ι.naturality c) y'
    rw [← hx, ← hy]
    simpa using hb.symm.trans ((congrArg (R.ι.app r) he).trans hc')
  have : IsIso μ := (ConcreteCategory.isIso_iff_bijective μ).mpr ⟨hinj, hsurj⟩
  let q : R.pt ≅ K.pt := asIso μ
  refine ⟨R, q, ⟨colimit.isColimit D⟩, ?_⟩
  intro t
  change Arrow.mk (R.ι.app t ≫ μ ≫ _) = _
  rw [← Category.assoc, hμ t]
  obtain ⟨e, he⟩ := hformula t
  rw [he]
  have hn := (colimit.desc B (Cocone.mk T γ)).naturality (eqToHom (congrArg op e))
  simp only [eqToHom_map] at hn
  rw [Category.assoc, Category.assoc, Category.assoc, hn]
  simp only [← Category.assoc, colimit.ι_desc_app]
  rw [Arrow.arrow_mk_comp_eqToHom, Category.assoc, ha]


end CategoryTheory
