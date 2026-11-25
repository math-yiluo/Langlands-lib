/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientLocalization

/-! # Section maps for normalized native restriction -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The additive section isomorphism induced by the actual inverse-image comparison.
Source: Stacks 03CE and the specified native inverse-image/localization isomorphism
(blueprint: lem-sf-adic-slice-restriction-linear). -/
noncomputable def adicSliceSectionEquiv {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (P : AdicModuleSectionComparison l X)
    (Q : AdicModuleSectionComparison l U.left)
    (c : Q.ring ≅ (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj P.ring)
    (M : AdicSheaf l X) (V : U.left.ProEtᵒᵖ) :
    (Q.E.functor.obj ((adicUpperStar l U.hom).obj M)).val.obj V ≃+
      ((adicComparisonRestriction U P Q c).obj (P.E.functor.obj M)).val.obj V :=
  (Q.sectionsEquiv _ V).symm.trans
    (((((sheafToPresheaf _ _).mapIso
      ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop).app M.X)).app
        V).toLinearEquiv).toAddEquiv.trans
      (P.sectionsEquiv M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))))

@[instance_reducible]
private noncomputable def restrictionLax {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : WeaklyEtale f) :
    (localizationRestriction (WeilCoefficients.{u} l) f hf).LaxMonoidal :=
  inferInstanceAs ((MorphismProperty.Over.map (f := f) ⊤ hf).sheafPushforwardContinuous
    (WeilCoefficients.{u} l) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Y)).LaxMonoidal

attribute [local instance] restrictionLax

private theorem restriction_comparison_tensor {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (U : X.ProEt)
    (S T : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    let F := upperStar (WeilCoefficients.{u} l) U.hom
    let L := localizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
    let e := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
    Functor.LaxMonoidal.μ F S T ≫ e.hom.app (S ⊗ T) =
      (e.hom.app S ⊗ₘ e.hom.app T) ≫ Functor.LaxMonoidal.μ L S T := by
  exact NatTrans.IsMonoidal.tensor
    (τ := (upperStarIsoSheafPushforward (WeilCoefficients.{u} l) U.hom U.prop).hom) S T

private theorem restriction_coefficient {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) :
    upperStarAdicConstantSheafHom l U.hom ≫
      (adicConstantSheafLocalizationRestrictionIso l U.hom U.prop).inv =
        (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
          U.hom U.prop).hom.app (adicConstantSheaf l X) := by
  rw [comparisonNativeCoefficient U.hom U.prop, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rfl

private theorem restriction_action {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M : AdicSheaf l X) :
    let L := localizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
    let e := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
    Mod.act ((adicUpperStar l U.hom).obj M).X ≫ e.hom.app M.X =
      ((adicConstantSheafLocalizationRestrictionIso l U.hom U.prop).inv ⊗ₘ
        e.hom.app M.X) ≫ Functor.LaxMonoidal.μ L (adicConstantSheaf l X) M.X ≫
          L.map (Mod.act M.X) := by
  dsimp only
  let F := upperStar (WeilCoefficients.{u} l) U.hom
  let L := localizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
  let e := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop
  let ψ := upperStarAdicConstantSheafHom l U.hom
  have hi : inv ψ ≫ e.hom.app (adicConstantSheaf l X) =
      (adicConstantSheafLocalizationRestrictionIso l U.hom U.prop).inv := by
    rw [← restriction_coefficient U, IsIso.inv_hom_id_assoc]
  change (inv ψ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F _ M.X ≫
    F.map (Mod.act M.X)) ≫ e.hom.app M.X = _
  simp only [Category.assoc]
  rw [e.hom.naturality, ← Category.assoc (Functor.LaxMonoidal.μ F _ M.X),
    restriction_comparison_tensor U]
  simp only [Category.assoc]
  rw [tensorHom_def]
  simp only [Category.assoc]
  erw [← comp_whiskerRight_assoc, hi]
  rfl

private theorem restriction_action_sections {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (U : X.ProEt) (M : AdicSheaf l X) (V : U.left.ProEtᵒᵖ)
    (a : (adicConstantSheaf l U.left).obj.obj V)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V) :
    adicComparisonPullSection U M V
      ((Mod.act ((adicUpperStar l U.hom).obj M).X).hom.app V
        ((Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
          (adicConstantSheaf l U.left) ((adicUpperStar l U.hom).obj M).X).app V
            (a ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x))) =
      (Mod.act M.X).hom.app
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X)
          (adicConstantSheaf l X) M.X).app
            (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
              (a ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)]
                adicComparisonPullSection U M V x)) := by
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (V := U.left) (U := X) U.prop
  let i := sheafToPresheaf (Scheme.ProEt.topology U.left) (WeilCoefficients.{u} l)
  have h := congrArg (fun f ↦ Functor.LaxMonoidal.μ i
    (adicConstantSheaf l U.left) ((adicUpperStar l U.hom).obj M).X ≫ i.map f)
      (restriction_action U M)
  simp only [Functor.map_comp] at h
  rw [← Functor.LaxMonoidal.μ_natural_assoc] at h
  dsimp only [i, localizationRestriction] at h
  have hV := congr_app h V
  simp only [NatTrans.comp_app, ObjectProperty.ι_map] at hV
  have hpush := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop) (WeilCoefficients.{u} l)
    (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) (adicConstantSheaf l X) M.X V
  erw [reassoc_of% hpush] at hV
  have hx := ConcreteCategory.congr_hom hV
    (a ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)
  exact hx

private theorem restriction_sections_apply {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (P : AdicModuleSectionComparison l X)
    (Q : AdicModuleSectionComparison l U.left)
    (c : Q.ring ≅ (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj P.ring)
    (M : AdicSheaf l X) (V : U.left.ProEtᵒᵖ)
    (y : ((adicUpperStar l U.hom).obj M).X.obj.obj V) :
    adicSliceSectionEquiv U P Q c M V
      (Q.sectionsEquiv ((adicUpperStar l U.hom).obj M) V y) =
        P.sectionsEquiv M
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
            (adicComparisonPullSection U M V y) := by
  simp only [adicSliceSectionEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

/-- Native restriction on sections respects the restricted coefficient action.
Source: Stacks 03CE, 03EK and 0E8H; the action step of normalized module restriction
(blueprint: lem-sf-adic-slice-restriction-linear).

Proof: identify inverse image along the site object with literal restriction,
using its distinguished initial indexing object. Under the specified identity
of coefficient functions the native coefficient structure morphism becomes the
identity. The monoidal inverse-image comparison carries the pulled-back internal
action to the original action on the composed object. Evaluate this equality on
the pure tensor of the coefficient and the section. The two base action formulas
identify its two sides with the scalar actions displayed here, and the supplied
section equivalences identify its underlying map with adicSliceSectionEquiv.
This argument uses arbitrary local coefficient functions and arbitrary sections;
it imposes no flatness or finite-rank hypothesis. -/
theorem adicSliceSectionEquiv_smul {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (P : AdicModuleSectionComparison l X)
    (Q : AdicModuleSectionComparison l U.left)
    (c : Q.ring ≅ (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj P.ring)
    (hc : ∀ (V : U.left.ProEtᵒᵖ) (a : Q.ring.obj.obj V),
      HEq ((c.hom.hom.app V) a) a)
    (M : AdicSheaf l X) (V : U.left.ProEtᵒᵖ)
    (a : Q.ring.obj.obj V)
    (x : (Q.E.functor.obj ((adicUpperStar l U.hom).obj M)).val.obj V) :
    adicSliceSectionEquiv U P Q c M V (a • x) =
      a • adicSliceSectionEquiv U P Q c M V x := by
  obtain ⟨y, rfl⟩ := (Q.sectionsEquiv ((adicUpperStar l U.hom).obj M) V).surjective x
  let W := op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)
  let z := (Mod.act ((adicUpperStar l U.hom).obj M).X).hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
      (adicConstantSheaf l U.left) ((adicUpperStar l U.hom).obj M).X).app V
        (Q.coefficient V a ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))
  have hq := Q.action ((adicUpperStar l U.hom).obj M) V a y
  have ha : P.coefficient W (c.hom.hom.app V a) = Q.coefficient V a := by
    apply eq_of_heq
    exact (P.coefficient_identity W _).trans ((hc V a).trans
      (Q.coefficient_identity V a).symm)
  calc
    _ = adicSliceSectionEquiv U P Q c M V
        (Q.sectionsEquiv ((adicUpperStar l U.hom).obj M) V z) :=
      congrArg (adicSliceSectionEquiv U P Q c M V) hq.symm
    _ = P.sectionsEquiv M W (adicComparisonPullSection U M V z) :=
      restriction_sections_apply U P Q c M V z
    _ = a • adicSliceSectionEquiv U P Q c M V
        (Q.sectionsEquiv ((adicUpperStar l U.hom).obj M) V y) := by
      rw [restriction_sections_apply]
      change P.sectionsEquiv M W (adicComparisonPullSection U M V z) =
        (c.hom.hom.app V a) • P.sectionsEquiv M W (adicComparisonPullSection U M V y)
      dsimp only [z]
      rw [restriction_action_sections, ← ha]
      exact P.action M W (c.hom.hom.app V a) (adicComparisonPullSection U M V y)

end AlgebraicGeometry.ProEtale
