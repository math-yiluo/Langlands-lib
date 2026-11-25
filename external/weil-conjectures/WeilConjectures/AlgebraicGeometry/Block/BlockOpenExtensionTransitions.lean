/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.OpenUnitSections.OpenSystemUnitSections

/-! # Horizontal compatibility of open extension under block reindexing

Source: Zheng Construction 4.1, ordinary levelwise operations; Stacks 03DI--03DJ.
(blueprint: lem-pur-block-open-extension-transitions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
open OpenUnitSections

attribute [local irreducible] systemRing ringPresheaf rings

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (t : SystemBlockMap) (U : C)
  (R : SystemBlockRepetition J B τ t)
  (Q : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U) ⥤
    Systems (J.over U) (openRings.{c, v, r} J (blockCoefficients B t) U)
      (openTransitions.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U))
  (qev : ∀ m : ℕ,
    Q ⋙ evaluation (J.over U) (openRings.{c, v, r} J (blockCoefficients B t) U)
      (openTransitions.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U) m ≅
    evaluation (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U) (t.index m))
  (O : OpenSystems.{c, v, r} J B τ U)
  (OD : OpenSystems.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U)

/-- The component comparison is the composite of the given ordinary evaluations.
Source: Zheng Construction 4.1; Stacks 03DJ.
(blueprint: lem-pur-block-open-extension-transitions) -/
@[irreducible] def blockOpenExtensionComponent
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) :
    (evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m).obj
        (OD.extension.obj (Q.obj P)) ≅
      (evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m).obj
        (R.repetition.obj (O.extension.obj P)) :=
  (OD.extensionEvaluation m).app (Q.obj P) ≪≫
    (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
      (abelianSheafify.{c, v, max c v r} J)
      (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).mapIso
      ((qev m).app P) ≪≫
    ((O.extensionEvaluation (t.index m)).app P).symm ≪≫
    ((R.evaluation m).app (O.extension.obj P)).symm

private theorem iso_conjugation
    {D : Type*} [Category D] {A B C E F : D}
    (e₁ : A ≅ B) (e₂ : B ≅ C) (e₃ : E ≅ C) (e₄ : F ≅ E) :
    (e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ e₄.symm).hom ≫ e₄.hom ≫ e₃.hom = e₁.hom ≫ e₂.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem component_conjugation
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) :
    (blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom ≫
        (R.evaluation m).hom.app (O.extension.obj P) ≫
        (O.extensionEvaluation (t.index m)).hom.app P =
      (OD.extensionEvaluation m).hom.app (Q.obj P) ≫
        (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
          (abelianSheafify.{c, v, max c v r} J)
          (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).map
            ((qev m).hom.app P) := by
  unfold blockOpenExtensionComponent
  exact iso_conjugation ((OD.extensionEvaluation m).app (Q.obj P))
    ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
      (abelianSheafify.{c, v, max c v r} J)
      (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).mapIso ((qev m).app P))
    ((O.extensionEvaluation (t.index m)).app P)
    ((R.evaluation m).app (O.extension.obj P))

private theorem section_cast_congr
    {D : Type*} [Category D] {K : GrothendieckTopology D} {A : Sheaf K RingCat.{u}}
    {M N : SheafOfModules.{u} A} {f g : M ⟶ N} (h : f = g) (V : Dᵒᵖ)
    {X Y : Type u} (hM : (M.val.obj V : Type u) = X) (hN : (N.val.obj V : Type u) = Y)
    (x : X) : castMap (fun z ↦ f.val.app V z) hM hN x =
      castMap (fun z ↦ g.val.app V z) hM hN x := by cases h; rfl

private def rawQ
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) (V : (Over U)ᵒᵖ) :=
  castMap (fun x ↦ ((qev m).hom.app P).val.app V x)
    (evaluation_type.{max c v, v, r} (J.over U)
      (openRings.{c, v, r} J (blockCoefficients B t) U)
      (openTransitions.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U)
      (Q.obj P) m V)
    (evaluation_type.{max c v, v, r} (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U) P (t.index m) V)

private def rawComponent
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) (V : Cᵒᵖ) :=
  castMap (fun x ↦ (blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom.val.app V x)
    (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
      (OD.extension.obj (Q.obj P)) m V)
    (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
      (R.repetition.obj (O.extension.obj P)) m V)

private def rawRepetitionEvaluation (M : Systems J B τ) (m : ℕ) (V : Cᵒᵖ) :=
  castMap (fun x ↦ ((R.evaluation m).hom.app M).val.app V x)
    (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
      (R.repetition.obj M) m V)
    (evaluation_type.{c, v, r} J B τ M (t.index m) V)

private theorem rawQ_heq
    (hqev : ∀ (m : ℕ) M V x, HEq (((qev m).hom.app M).val.app V x) x)
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) (V : (Over U)ᵒᵖ)
    (x : (Q.obj P).val.obj (op (m, V.unop))) : HEq (rawQ.{c, v, r} J B τ t U Q qev P m V x) x := by
  unfold rawQ
  exact (castMap_heq _ _ _ x).trans ((hqev m P V _).trans (cast_heq _ _))

private theorem rawRepetitionEvaluation_heq
    (M : Systems J B τ) (m : ℕ) (V : Cᵒᵖ)
    (x : (R.repetition.obj M).val.obj (op (m, V.unop))) :
    HEq (rawRepetitionEvaluation.{c, v, r} J B τ t R M m V x) x := by
  unfold rawRepetitionEvaluation
  exact (castMap_heq _ _ _ x).trans ((R.evaluation_sections m M V _).trans (cast_heq _ _))

private theorem rawComponent_unit
    (hO : ∀ (n : ℕ) N V x,
      HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x)
    (hOD : ∀ (n : ℕ) N V x,
      HEq (((OD.restrictionEvaluation n).hom.app N).val.app V x) x)
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (m : ℕ) (V : (Over U)ᵒᵖ)
    (x : (Q.obj P).val.obj (op (m, V.unop))) :
    HEq (rawComponent.{c, v, r} J B τ t U R Q qev O OD P m (op V.unop.left)
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
        (op (m, V.unop)) x))
      (rawUnit.{c, v, r} J B τ U O P (op (t.index m, V.unop))
        (rawQ.{c, v, r} J B τ t U Q qev P m V x)) := by
  have he :
      rawRepetitionEvaluation.{c, v, r} J B τ t R (O.extension.obj P) m (op V.unop.left)
        (rawComponent.{c, v, r} J B τ t U R Q qev O OD P m (op V.unop.left)
          (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
            (op (m, V.unop)) x)) =
      rawUnit.{c, v, r} J B τ U O P (op (t.index m, V.unop))
        (rawQ.{c, v, r} J B τ t U Q qev P m V x) := by
    apply castMap_injective _
      (evaluation_type.{c, v, r} J B τ (O.extension.obj P) (t.index m) (op V.unop.left)) rfl
      (iso_section_injective ((O.extensionEvaluation (t.index m)).app P) (op V.unop.left))
    have hc := section_cast_congr
      (component_conjugation.{c, v, r} J B τ t U R Q qev O OD P m) (op V.unop.left)
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (OD.extension.obj (Q.obj P)) m (op V.unop.left)) rfl
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
        (op (m, V.unop)) x)
    have hl := congrFun (section_cast_triple
      (blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom
      ((R.evaluation m).hom.app (O.extension.obj P))
      ((O.extensionEvaluation (t.index m)).hom.app P) (op V.unop.left)
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (OD.extension.obj (Q.obj P)) m (op V.unop.left))
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (R.repetition.obj (O.extension.obj P)) m (op V.unop.left))
      (evaluation_type.{c, v, r} J B τ (O.extension.obj P) (t.index m) (op V.unop.left)) rfl)
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        U OD (Q.obj P) (op (m, V.unop)) x)
    have hr := congrFun (section_cast_comp ((OD.extensionEvaluation m).hom.app (Q.obj P))
      ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
        (abelianSheafify.{c, v, max c v r} J)
        (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).map ((qev m).hom.app P))
      (op V.unop.left)
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (OD.extension.obj (Q.obj P)) m (op V.unop.left)) rfl rfl)
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        U OD (Q.obj P) (op (m, V.unop)) x)
    have hc' := hl.symm.trans (hc.trans hr)
    change rawExtensionEvaluation.{c, v, r} J B τ U O P (t.index m) (op V.unop.left) _ =
      ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
        (abelianSheafify.{c, v, max c v r} J)
        (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).map
          ((qev m).hom.app P)).val.app (op V.unop.left)
            (rawExtensionEvaluation.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
              U OD (Q.obj P) m (op V.unop.left)
              (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
                (op (m, V.unop)) x)) at hc'
    change rawExtensionEvaluation.{c, v, r} J B τ U O P (t.index m) (op V.unop.left) _ =
      rawExtensionEvaluation.{c, v, r} J B τ U O P (t.index m) (op V.unop.left) _
    have ho := rawUnit_evaluation.{c, v, r} J B τ U O hO P (t.index m) V
      (rawQ.{c, v, r} J B τ t U Q qev P m V x)
    have hd := rawUnit_evaluation.{c, v, r} J (blockCoefficients B t)
      (blockTransitions J B τ t) U OD hOD (Q.obj P) m V x
    have hn := @localized_unit_naturality_cast.{c, v, r} C _ J
      (abelianSheafify.{c, v, max c v r} J)
      (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U _ _
      ((qev m).hom.app P) V
      (cast (evaluation_type.{max c v, v, r} (J.over U)
        (openRings.{c, v, r} J (blockCoefficients B t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U)
        (Q.obj P) m V).symm x)
    have hd' := congrArg
      (fun z ↦ ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
        (abelianSheafify.{c, v, max c v r} J)
        (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U).map
          ((qev m).hom.app P)).val.app (op V.unop.left) z) hd
    have hh := hc'.trans (hd'.trans hn)
    have ho' := ho
    simp only [rawQ, castMap, cast_cast, cast_eq] at ho'
    exact hh.trans ho'.symm
  exact (rawRepetitionEvaluation_heq.{c, v, r} J B τ t R (O.extension.obj P) m
    (op V.unop.left) _).symm.trans (heq_of_eq he)

private theorem comparison_evaluation
    {A A' B B' K L : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Category K] [Category L]
    (Q : A ⥤ A') (D : A' ⥤ B') (O : A ⥤ B) (R : B ⥤ B')
    (E : B' ⥤ K) (E₀ : B ⥤ K) (F' : A' ⥤ L) (F : A ⥤ L) (j : L ⥤ K)
    (a : D ⋙ E ≅ F' ⋙ j) (q : Q ⋙ F' ≅ F) (b : O ⋙ E₀ ≅ F ⋙ j)
    (r : R ⋙ E ≅ E₀) (P : A) :
    (Functor.associator Q D E ≪≫ Functor.isoWhiskerLeft Q a ≪≫
      (Functor.associator Q F' j).symm ≪≫ Functor.isoWhiskerRight q j ≪≫ b.symm ≪≫
      Functor.isoWhiskerLeft O r.symm ≪≫ (Functor.associator O R E).symm).hom.app P =
    (a.app (Q.obj P) ≪≫ j.mapIso (q.app P) ≪≫ (b.app P).symm ≪≫
      (r.app (O.obj P)).symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.id_comp, Category.comp_id]

/-- The explicit component comparisons are natural in the open system.
Source: naturality of the four factors defining the component comparison.
(blueprint: lem-pur-block-open-extension-transitions) -/
@[irreducible] def blockOpenExtensionEvaluationIso (m : ℕ) :
    (Q ⋙ OD.extension) ⋙
        evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m ≅
      (O.extension ⋙ R.repetition) ⋙
        evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m :=
  let L := @SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) (B (t.index m)) U
  Functor.associator Q OD.extension _ ≪≫
    Functor.isoWhiskerLeft Q (OD.extensionEvaluation m) ≪≫
    (Functor.associator Q _ L).symm ≪≫ Functor.isoWhiskerRight (qev m) L ≪≫
    (O.extensionEvaluation (t.index m)).symm ≪≫
    Functor.isoWhiskerLeft O.extension (R.evaluation m).symm ≪≫
    (Functor.associator O.extension R.repetition _).symm

/-- Evaluation of the natural comparison is the explicit four-factor component.
Source: the component formulas for whiskering and functor associators.
(blueprint: lem-pur-block-open-extension-transitions) -/
theorem blockOpenExtensionEvaluationIso_hom (m : ℕ) (P) :
    (blockOpenExtensionEvaluationIso J B τ t U R Q qev O OD m).hom.app P =
      (blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom := by
  unfold blockOpenExtensionEvaluationIso blockOpenExtensionComponent
  exact comparison_evaluation Q OD.extension O.extension R.repetition _ _ _ _ _
    (OD.extensionEvaluation m) (qev m) (O.extensionEvaluation (t.index m)) (R.evaluation m) P

/-- The normalized component comparisons commute with horizontal system transitions.
Source: Zheng Construction 4.1, ordinary levelwise operations, and Stacks 03DI--03DJ.
(blueprint: lem-pur-block-open-extension-transitions).

Proof: write [φ,x] for the summand generator associated to a section x of
P at (t(m),V→U). The unit evaluation identities for O and OD say that their
extension evaluations carry the system-adjunction unit to precisely this
summand generator. Since their restriction evaluations and qev are identities
on sections, d_m sends [φ,x] to the identical generator under repetition.
The ordinary system units are morphisms of systems. Their horizontal
naturality therefore sends [φ,x] along m→n to [φ,P_(t(m)→t(n))(x)], both
before and after d. The hypothesis hQ supplies this exact transition for QP.
Thus both proposed composites agree on every summand generator. The open
adjunction, or equivalently the direct-sum presentation followed by
sheafification, says that maps out of the extension are determined by these
generators. Undo the extension evaluation isomorphism at m to obtain the
claimed equality. The scalar action uses the same composite coefficient map
from t(m) to t(n), by functoriality of rings. Inside a block this is the
identity transition; at a boundary it is the original coefficient transition.
This also treats singleton blocks, identity repetition and zero coefficients;
no flatness of coefficient maps is needed. -/
theorem blockOpenExtensionComponent_transition
    (hQ : ∀ (M : Systems (J.over U) (openRings.{c, v, r} J B U)
        (openTransitions.{c, v, r} J B τ U))
      {V W : (ℕ × Over U)ᵒᵖ} (f : V ⟶ W),
      HEq (fun x ↦ (Q.obj M).val.map f x)
        (fun x ↦ M.val.map ((blockSite (C := Over U) t.index).map f.unop).op x))
    (hqev : ∀ (m : ℕ) M V x, HEq (((qev m).hom.app M).val.app V x) x)
    (hO : ∀ (n : ℕ) N V x,
      HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x)
    (hOD : ∀ (n : ℕ) N V x,
      HEq (((OD.restrictionEvaluation n).hom.app N).val.app V x) x)
    (P : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) {m n : ℕ} (h : n ≤ m) :
    (transition J (blockCoefficients B t) (blockTransitions J B τ t) h).app
        (OD.extension.obj (Q.obj P)) ≫
      (res (coefficientMap J (blockCoefficients B t) (blockTransitions J B τ t) h)).map
        (blockOpenExtensionComponent J B τ t U R Q qev O OD P n).hom =
    (blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom ≫
      (transition J (blockCoefficients B t) (blockTransitions J B τ t) h).app
        (R.repetition.obj (O.extension.obj P))  := by
  apply open_level_hom_ext_raw.{c, v, r} J (blockCoefficients B t)
    (blockTransitions J B τ t) U OD hOD (Q.obj P) m
  intro V x
  let f : op (m, V.unop) ⟶ op (n, V.unop) :=
    (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
  let k : op (t.index m, V.unop) ⟶ op (t.index n, V.unop) :=
    ((blockSite (C := Over U) t.index).map f.unop).op
  let b : op (m, V.unop.left) ⟶ op (n, V.unop.left) :=
    (Prod.mkHom (homOfLE h) (𝟙 V.unop.left)).op
  let a : op (t.index m, V.unop.left) ⟶ op (t.index n, V.unop.left) :=
    ((blockSite (C := C) t.index).map b.unop).op
  have hD := rawUnit_naturality.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
    U OD (Q.obj P) f x
  change rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
      (op (n, V.unop)) ((Q.obj P).val.map f x) =
    (OD.extension.obj (Q.obj P)).val.map b
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
        (op (m, V.unop)) x) at hD
  have hA := rawUnit_naturality.{c, v, r} J B τ U O P k (rawQ.{c, v, r} J B τ t U Q qev P m V x)
  change rawUnit.{c, v, r} J B τ U O P (op (t.index n, V.unop))
      (P.val.map k (rawQ.{c, v, r} J B τ t U Q qev P m V x)) =
    (O.extension.obj P).val.map a
      (rawUnit.{c, v, r} J B τ U O P (op (t.index m, V.unop))
        (rawQ.{c, v, r} J B τ t U Q qev P m V x)) at hA
  have hq : rawQ.{c, v, r} J B τ t U Q qev P n V ((Q.obj P).val.map f x) =
      P.val.map k (rawQ.{c, v, r} J B τ t U Q qev P m V x) := by
    exact eq_of_heq ((rawQ_heq.{c, v, r} J B τ t U Q qev hqev P n V _).trans
      (apply_heq (type_eq_of_heq (rawQ_heq.{c, v, r} J B τ t U Q qev hqev P n V 0)).symm
        (hQ P f) (rawQ_heq.{c, v, r} J B τ t U Q qev hqev P m V x).symm))
  have hleft := rawComponent_unit.{c, v, r} J B τ t U R Q qev O OD hO hOD P n V
    ((Q.obj P).val.map f x)
  have hright := apply_heq
    (type_eq_of_heq (rawRepetitionEvaluation_heq.{c, v, r} J B τ t R
      (O.extension.obj P) n (op V.unop.left) 0)).symm
    (R.repeat_restrictions (O.extension.obj P) b)
    (rawComponent_unit.{c, v, r} J B τ t U R Q qev O OD hO hOD P m V x)
  change HEq _ ((O.extension.obj P).val.map a _) at hright
  rw [← hA] at hright
  rw [hq] at hleft
  let hsrc := evaluation_type.{c, v, r} J (blockCoefficients B t)
    (blockTransitions J B τ t) (OD.extension.obj (Q.obj P)) m (op V.unop.left)
  let hout := (res_type.{c, v, r} J
    (coefficientMap J (blockCoefficients B t) (blockTransitions J B τ t) h)
    ((evaluation J (blockCoefficients B t) (blockTransitions J B τ t) n).obj
      (R.repetition.obj (O.extension.obj P))) (op V.unop.left)).trans
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (R.repetition.obj (O.extension.obj P)) n (op V.unop.left))
  apply (cast_inj hout).mp
  change castMap (fun z ↦
      ((transition J (blockCoefficients B t) (blockTransitions J B τ t) h).app
        (OD.extension.obj (Q.obj P)) ≫
      (res (coefficientMap J (blockCoefficients B t) (blockTransitions J B τ t) h)).map
        (blockOpenExtensionComponent J B τ t U R Q qev O OD P n).hom).val.app
          (op V.unop.left) z)
      hsrc hout
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        U OD (Q.obj P) (op (m, V.unop)) x) =
    castMap (fun z ↦
      ((blockOpenExtensionComponent J B τ t U R Q qev O OD P m).hom ≫
        (transition J (blockCoefficients B t) (blockTransitions J B τ t) h).app
          (R.repetition.obj (O.extension.obj P))).val.app (op V.unop.left) z) hsrc hout
      (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        U OD (Q.obj P) (op (m, V.unop)) x)
  erw [section_cast_comp _ _ (op V.unop.left) hsrc
    ((res_type.{c, v, r} J (coefficientMap J (blockCoefficients B t) (blockTransitions J B τ t) h)
      ((evaluation J (blockCoefficients B t) (blockTransitions J B τ t) n).obj
        (OD.extension.obj (Q.obj P))) (op V.unop.left)).trans
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (OD.extension.obj (Q.obj P)) n (op V.unop.left))) hout,
    section_cast_comp _ _ (op V.unop.left) hsrc
      (evaluation_type.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t)
        (R.repetition.obj (O.extension.obj P)) m (op V.unop.left)) hout]
  dsimp only [Function.comp_apply]
  erw [res_map_cast.{c, v, r} J, transition_cast.{c, v, r}, transition_cast.{c, v, r}]
  change rawComponent.{c, v, r} J B τ t U R Q qev O OD P n (op V.unop.left)
      ((OD.extension.obj (Q.obj P)).val.map b
        (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
          (op (m, V.unop)) x)) =
    (R.repetition.obj (O.extension.obj P)).val.map b
      (rawComponent.{c, v, r} J B τ t U R Q qev O OD P m (op V.unop.left)
        (rawUnit.{c, v, r} J (blockCoefficients B t) (blockTransitions J B τ t) U OD (Q.obj P)
          (op (m, V.unop)) x))
  rw [← hD]
  exact eq_of_heq (hleft.trans hright.symm)

end WeilConjectures.SemilinearSections
