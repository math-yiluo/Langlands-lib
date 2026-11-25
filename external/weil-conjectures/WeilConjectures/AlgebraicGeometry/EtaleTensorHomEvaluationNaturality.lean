/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Naturality of the tensor-sections evaluation map

Source: Stacks Project, Tags 03DT and 03DR
(blueprint: lem-sc-etale-tensor-sections-evaluation-naturality).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The comparison of tensor pullback with abstract pullback normalized by their units.
Source: Stacks Project, Tag 0096; uniqueness of left adjoints. -/
def tensorSectionsPullbackComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    tensorPullback f ≅ pullback f :=
  Adjunction.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
    (pullbackPushforwardAdjunction f)

/-- Evaluate a pulled-back module map at one after identifying its source with the
structure sheaf and its target with tensor pullback.
Source: Stacks Project, Tag 03DT, proof of Lemma 35.8.1. -/
def etaleTensorHomEvaluation {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)
    (φ : (etaleHom (unitObj X) F).obj (.op U)) :
    Γ((tensorPullback U.hom).obj F, ⊤) :=
  ((pullbackObjUnitIso U.hom).inv ≫ φ ≫
    (tensorSectionsPullbackComparison U.hom).inv.app F).app ⊤ (1 : Γ(U.left, ⊤))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_comp_inv {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    (tensorSectionsPullbackComparison (a ≫ b)).inv ≫ (tensorSectionsComp a b).inv =
      (pullbackComp a b).inv ≫
        Functor.whiskerLeft (pullback b) (tensorSectionsPullbackComparison a).inv ≫
        Functor.whiskerRight (tensorSectionsPullbackComparison b).inv (tensorPullback a) := by
  apply (conjugateEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))
    (pullbackPushforwardAdjunction (a ≫ b))).injective
  rw [← conjugateEquiv_comp _ (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction b).comp (Classical.choose
        (exists_tensorPullbackAdjunction a)))]
  simp only [tensorSectionsPullbackComparison, conjugateEquiv_leftAdjointUniq_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, Category.comp_id,
    conjugateEquiv_pullbackComp_inv]
  change (conjugateEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))
    (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))))
      ((conjugateEquiv
        ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
          (Classical.choose (exists_tensorPullbackAdjunction a)))
        (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))).symm
        (pushforwardComp a b).hom) = _
  rw [Equiv.apply_symm_apply]
  erw [Functor.whiskerLeft_id, Functor.whiskerRight_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    (tensorSectionsComp a b).hom ≫ (tensorSectionsPullbackComparison (a ≫ b)).hom =
      Functor.whiskerRight (tensorSectionsPullbackComparison b).hom (tensorPullback a) ≫
        Functor.whiskerLeft (pullback b) (tensorSectionsPullbackComparison a).hom ≫
        (pullbackComp a b).hom := by
  have h : tensorSectionsComp a b ≪≫ tensorSectionsPullbackComparison (a ≫ b) =
      Functor.isoWhiskerRight (tensorSectionsPullbackComparison b) (tensorPullback a) ≪≫
        Functor.isoWhiskerLeft (pullback b) (tensorSectionsPullbackComparison a) ≪≫
        pullbackComp a b := by
    apply Iso.ext_inv
    exact comparison_comp_inv a b
  exact congrArg Iso.hom h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_unit {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules)
    (s : Γ(G, ⊤)) :
    ((tensorSectionsPullbackComparison a).hom.app G).app ⊤ (tensorSectionsUnit a G s) =
      pullbackSection a s := by
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj G).presheaf.map_id, Category.comp_id]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Classical.choose (exists_tensorPullbackAdjunction a)) (pullbackPushforwardAdjunction a) G
  have hs := congrArg (fun φ ↦ φ.app ⊤ s) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_section {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (F : C.Modules) (s : Γ((tensorPullback b).obj F, ⊤)) :
    ((tensorSectionsPullbackComparison (a ≫ b)).hom.app F).app ⊤
        (((tensorSectionsComp a b).hom.app F).app ⊤
          (tensorSectionsUnit a ((tensorPullback b).obj F) s)) =
      ((pullbackComp a b).hom.app F).app ⊤
        (pullbackSection a (((tensorSectionsPullbackComparison b).hom.app F).app ⊤ s)) := by
  have hc := congrArg (fun φ ↦ (φ.app F).app ⊤
      (tensorSectionsUnit a ((tensorPullback b).obj F) s)) (comparison_comp a b)
  simp only [NatTrans.comp_app, Hom.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ConcreteCategory.comp_apply] at hc
  rw [hc]
  have hn := congrArg (fun φ ↦ φ.app ⊤ s)
    ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.naturality
      ((tensorSectionsPullbackComparison b).hom.app F))
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  have hn' : ((tensorPullback a).map ((tensorSectionsPullbackComparison b).hom.app F)).app ⊤
        (tensorSectionsUnit a ((tensorPullback b).obj F) s) =
      tensorSectionsUnit a ((pullback b).obj F)
        (((tensorSectionsPullbackComparison b).hom.app F).app ⊤ s) := by
    unfold tensorSectionsUnit
    erw [hi, ((tensorPullback a).obj ((tensorPullback b).obj F)).presheaf.map_id,
      ((tensorPullback a).obj ((pullback b).obj F)).presheaf.map_id, Category.comp_id,
      Category.comp_id]
    simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map,
      Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at hn
    exact hn.symm
  exact congrArg (((pullbackComp a b).hom.app F).app ⊤)
    ((congrArg (((tensorSectionsPullbackComparison a).hom.app ((pullback b).obj F)).app ⊤)
      hn').trans (comparison_unit a ((pullback b).obj F)
        (((tensorSectionsPullbackComparison b).hom.app F).app ⊤ s)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_restriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules)
    (s : Γ((tensorPullback b).obj F, ⊤)) :
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤
        (((tensorSectionsComp a b).hom.app F).app ⊤
          (tensorSectionsUnit a ((tensorPullback b).obj F) s)) =
      ((tensorSectionsPullbackComparison c).inv.app F).app ⊤
        ((eqToHom (congrArg (fun f ↦ (pullback f).obj F) h)).app ⊤
          (((pullbackComp a b).hom.app F).app ⊤
            (pullbackSection a
              (((tensorSectionsPullbackComparison b).hom.app F).app ⊤ s)))) := by
  subst c
  simp only [eqToHom_refl, Hom.id_app, ConcreteCategory.id_apply]
  have hc := comparison_section a b F s
  have hi := congrArg (fun φ ↦ φ.app ⊤
      (((tensorSectionsComp a b).hom.app F).app ⊤
        (tensorSectionsUnit a ((tensorPullback b).obj F) s)))
    (Iso.hom_inv_id_app (tensorSectionsPullbackComparison (a ≫ b)) F)
  simp only [Hom.comp_app, Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at hi
  exact hi.symm.trans (congrArg (((tensorSectionsPullbackComparison (a ≫ b)).inv.app F).app ⊤)
    hc)

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homSection_restriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules)
    (φ : (pullback b).obj (unit C) ⟶ (pullback b).obj F) :
    homSection c (pullHom (F := modulesPseudofunctor) φ a c c h h) =
      (eqToHom (congrArg (fun f ↦ (pullback f).obj F) h)).app ⊤
        (((pullbackComp a b).hom.app F).app ⊤ (pullbackSection a (homSection b φ))) := by
  subst c
  rw [pullHom_eq_pullbackComp]
  simp only [eqToHom_refl, Hom.id_app, ConcreteCategory.id_apply]
  exact homSection_comp b a φ

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem section_eval_restriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules)
    (φ : (pullback b).obj (unit C) ⟶ (pullback b).obj F) :
    ((tensorSectionsPullbackComparison c).inv.app F).app ⊤
        (homSection c (A := F) (pullHom (F := modulesPseudofunctor) φ a c c h h)) =
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤
        (((tensorSectionsComp a b).hom.app F).app ⊤
          (tensorSectionsUnit a ((tensorPullback b).obj F)
            (((tensorSectionsPullbackComparison b).inv.app F).app ⊤
              (homSection b (A := F) φ)))) := by
  have hi := congrArg (fun ψ ↦ ψ.app ⊤ (homSection b (A := F) φ))
    (Iso.inv_hom_id_app (tensorSectionsPullbackComparison b) F)
  simp only [Hom.comp_app, Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at hi
  have hc := comparison_restriction a b c h F
    (((tensorSectionsPullbackComparison b).inv.app F).app ⊤ (homSection b (A := F) φ))
  have he := congrArg (fun s : Γ((pullback b).obj F, ⊤) ↦
    ((tensorSectionsPullbackComparison c).inv.app F).app ⊤
      ((eqToHom (congrArg (fun f ↦ (pullback f).obj F) h)).app ⊤
        (((pullbackComp a b).hom.app F).app ⊤
          (pullbackSection a (M := (pullback b).obj F) (U := ⊤) s)))) hi
  have hk := congrArg (((tensorSectionsPullbackComparison c).inv.app F).app ⊤)
    (homSection_restriction a b c h F φ)
  exact hk.trans (hc.trans he).symm

private def restrictionOfEq {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules) :
    Γ((tensorPullback b).obj F, ⊤) ⟶ Γ((tensorPullback c).obj F, ⊤) :=
  tensorSectionsUnit a ((tensorPullback b).obj F) ≫
    ((tensorSectionsComp a b).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤

private def evaluationAt {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    ((pullback b).obj (unit B) ⟶ (pullback b).obj F) →
      Γ((tensorPullback b).obj F, ⊤) :=
  fun φ ↦ ((tensorSectionsPullbackComparison b).inv.app F).app ⊤ (homSection b φ)

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluationAt_restriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules) :
    TypeCat.ofHom (fun φ ↦ evaluationAt c F
        (pullHom (F := modulesPseudofunctor) φ a c c h h)) =
      TypeCat.ofHom (evaluationAt b F) ≫ TypeCat.ofHom (restrictionOfEq a b c h F) := by
  subst c
  apply ConcreteCategory.hom_ext
  intro φ
  exact section_eval_restriction a b (a ≫ b) rfl F φ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_eq_hom {X : Scheme.{u}} (F : X.Modules) (U : X.Etale) :
    TypeCat.ofHom (etaleTensorHomEvaluation F U) =
      TypeCat.ofHom (evaluationAt U.hom F) := by
  apply ConcreteCategory.hom_ext
  intro φ
  unfold evaluationAt homSection
  rw [pullbackSection_one_eq]
  rfl

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etaleHom_map_hom {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (etaleHom (unitObj X) F).map g =
      TypeCat.ofHom (fun φ ↦
        pullHom (F := modulesPseudofunctor) (M₁ := unitObj X) (M₂ := F)
          (f₁ := U.unop.hom) (f₂ := U.unop.hom) φ g.unop.left V.unop.hom V.unop.hom
          g.unop.w g.unop.w) := by
  rfl

private theorem sections_map_hom {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat).map g =
      TypeCat.ofHom (restrictionOfEq g.unop.left U.unop.hom V.unop.hom g.unop.w F) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of a pulled-back module map commutes with restriction on the etale site.
Source: Stacks Project, Tag 03DT, proof of Lemma 35.8.1, and Tag 03DR, (35.8.0.1).
(blueprint: lem-sc-etale-tensor-sections-evaluation-naturality).

Proof: Write e_f for the unit-normalized comparison between tensor and abstract
pullback. The conjugates of the two sides of
  e_(a b).inv ≫ tensorSectionsComp(a,b).inv =
  pullbackComp(a,b).inv ≫ whiskerLeft(pullback b,e_a.inv) ≫
  whiskerRight(e_b.inv,tensorPullback a)
are equal: conjugation takes e_f.inv to the identity, takes both composition
comparisons to pushforwardComp(a,b).hom, and respects composition and whiskering.
Injectivity of conjugation therefore proves this equation. Inverting it gives the
forward comparison equation. The unit equation of leftAdjointUniq identifies
 e_a.hom(tensorSectionsUnit a s) with pullbackSection a s. Naturality of the
adjunction unit also shows that tensorSectionsUnit commutes with any module map.
Thus applying e_(a b).hom to tensor restriction gives abstract restriction after
applying e_b.hom. Evaluation as defined here is e_b.inv applied to homSection b:
this follows from pullbackSection_one_eq. The existing homSection_comp theorem
then proves the desired equation for a composite a followed by b. Substitute the
equality g.left followed by U.hom equals V.hom to obtain the same equality
transport on both sides. Finally, etaleHom.map is precisely pullHom restricted
from the category of schemes over X. No quasi-coherence assumption or sheaf
condition is used. Identity arrows and empty schemes are included by the same
adjunction equations; the argument requires no nonempty set of sections. -/
theorem etaleTensorHomEvaluation_naturality {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (etaleHom (unitObj X) F).map g ≫
        TypeCat.ofHom (etaleTensorHomEvaluation F V.unop) =
      TypeCat.ofHom (etaleTensorHomEvaluation F U.unop) ≫
        (etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat).map g := by
  rw [evaluation_eq_hom, evaluation_eq_hom, etaleHom_map_hom, sections_map_hom]
  exact evaluationAt_restriction g.unop.left U.unop.hom V.unop.hom g.unop.w F

end
end AlgebraicGeometry.Scheme.Modules
