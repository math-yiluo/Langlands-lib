/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientFreeGenerator
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-! # The action of a normalized realization on sections

Source: diagonal coefficient changes, paragraph (1), coefficient identification.
(blueprint: lem-sfb-diagonal-completed-section-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj
namespace CategoryTheory.SheafModuleSection
universe c v d v' w
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J Ab.{w}] [HasWeakSheafify K Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [(K.W (A := Ab.{w})).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory

/-- Evaluate an internal action through the presheaf tensor comparison.
Source: sectionwise internal module actions
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def action {R : Sheaf J Ab.{w}} [MonObj R] (M : Mod (Sheaf J Ab.{w}) R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.X.obj.obj U) : M.X.obj.obj U :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{w}) R M.X).app U ≫
    (Mod.act M.X).hom.app U).hom (a ⊗ₜ[ℤ] x)

/-- Evaluate a coefficient morphism to direct image with the original section type.
Source: the sectionwise sheaf pushforward
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def pushScalar (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf J Ab.{w}} {S : Sheaf K Ab.{w}}
    (φ : R ⟶ (F.sheafPushforwardContinuous Ab.{w} J K).obj S)
    (U : Cᵒᵖ) (a : R.obj.obj U) : S.obj.obj (F.op.obj U) :=
  φ.hom.app U a

/-- Read scalar restriction and ordinary direct image on sections.
Source: the lax monoidal sheaf pushforward tensor comparison
(blueprint: lem-sfb-diagonal-completed-section-action).
Proof: naturality of the tensor comparison moves the coefficient map to the input.
The tensor comparison for direct image is the restriction of the original comparison. -/
theorem action_pushforward (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf J Ab.{w}} [MonObj R] {S : Sheaf K Ab.{w}} [MonObj S]
    (φ : R ⟶ (F.sheafPushforwardContinuous Ab.{w} J K).obj S) [IsMonHom φ]
    (M : Mod (Sheaf K Ab.{w}) S) (U : Cᵒᵖ) (a : R.obj.obj U)
    (x : M.X.obj.obj (F.op.obj U)) :
    action ((Mod.comap φ).obj
        (((F.sheafPushforwardContinuous Ab.{w} J K).mapMod S).obj M)) U a x =
      action M (F.op.obj U) (pushScalar F φ U a) x := by
  let H := F.sheafPushforwardContinuous Ab.{w} J K
  let i := sheafToPresheaf J Ab.{w}
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_left i φ (H.obj M.X)) U
  dsimp only [NatTrans.comp_app] at hn
  have hp := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    F Ab.{w} J K S M.X U
  have hn' := congrArg (fun q ↦ q ≫
    (Functor.LaxMonoidal.μ H S M.X).hom.app U ≫
      (H.map (Mod.act M.X)).hom.app U) hn.symm
  have hp' := congrArg (fun q ↦ (i.map φ ▷ i.obj (H.obj M.X)).app U ≫ q ≫
    (H.map (Mod.act M.X)).hom.app U) hp
  simp only [Category.assoc] at hn' hp'
  exact congrArg (fun q ↦ q.hom (a ⊗ₜ[ℤ] x)) (hn'.trans hp')

private theorem map_action {R : Sheaf J Ab.{w}} [MonObj R]
    {M N : Mod (Sheaf J Ab.{w}) R} (g : M ⟶ N)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.X.obj.obj U) :
    g.hom.hom.app U (action M U a x) = action N U a (g.hom.hom.app U x) := by
  have h := congrArg (fun f ↦ f.hom.app U)
    (Mod.act_hom g)
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_right
    (sheafToPresheaf J Ab.{w}) R g.hom) U
  have h' := congrArg (fun f ↦
    (Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{w}) R M.X).app U ≫ f) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h'
  have hn' := congrArg (fun f ↦ f ≫ (Mod.act N.X).hom.app U) hn.symm
  simp only [NatTrans.comp_app, Category.assoc] at hn'
  exact congrArg (fun f ↦ f.hom (a ⊗ₜ[ℤ] x)) (h'.trans hn')

/-- Sectionwise compatibility on pure tensors implies linearity of an internal map.
Source: the presheaf tensor comparison and pure-tensor extensionality
(blueprint: lem-sfb-diagonal-completed-section-action).
Proof: test equality after the tensor comparison, then on each sectionwise pure tensor. -/
theorem linear_of_action {R : Sheaf J Ab.{w}} [MonObj R]
    {M N : Mod (Sheaf J Ab.{w}) R} (g : M.X ⟶ N.X)
    (h : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.X.obj.obj U),
      g.hom.app U (action M U a x) = action N U a (g.hom.app U x)) :
    Mod.act M.X ≫ g = R ◁ g ≫ Mod.act N.X := by
  apply Sheaf.tensor_hom_ext
  apply NatTrans.ext
  funext U
  let i := sheafToPresheaf J Ab.{w}
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_right i R g) U
  dsimp only [NatTrans.comp_app] at hn
  change (Functor.LaxMonoidal.μ i R M.X).app U ≫
      (Mod.act M.X).hom.app U ≫ g.hom.app U =
    (Functor.LaxMonoidal.μ i R M.X).app U ≫
      (R ◁ g).hom.app U ≫ (Mod.act N.X).hom.app U
  simp only [← Category.assoc]
  erw [← hn]
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a x
  exact h U a x

end CategoryTheory.SheafModuleSection

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Evaluate an internal module action on two local sections, using the tensor comparison
from the presheaf tensor to the sheaf tensor. Source: the sectionwise description of internal
abelian module sheaves (blueprint: lem-sfb-diagonal-completed-section-action). -/
def coefficientSectionAction {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (N : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) (U : X.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U)
    (x : N.X.obj.obj U) : N.X.obj.obj U :=
  CategoryTheory.SheafModuleSection.action N U a x

/-- The underlying coefficient comparison fixed by the regular-module normalization.
Source: diagonal coefficient identification, paragraph (1)
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def completedRealizationScalarIso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) :
    (diagonalCompletedRestriction l X ⋙ diagonalForget l X).obj
        (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≅
      condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
  (e.underlying.app _).symm ≪≫ (Mod.forget _).mapIso e.unitIso

/-- The scalar comparison evaluated on actual completed coefficient sections.
Source: regular-module normalization
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def completedRealizationScalarSection {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) (U : X.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U) :
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U :=
  (completedRealizationScalarIso e).hom.hom.app U a

/-- The inverse scalar comparison as a map into actual completed coefficient sections.
Source: regular-module normalization of the realization
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def completedRealizationScalarInv {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) (U : X.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U) :
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U :=
  (completedRealizationScalarIso e).inv.hom.app U a

/-- Applying the scalar comparison after its typed inverse returns the original section.
Source: inverse cancellation for the regular-module comparison
(blueprint: lem-sfb-diagonal-completed-section-action).
Proof: evaluate the inverse-hom identity of completedRealizationScalarIso on the section. -/
theorem completedRealizationScalarInv_hom {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) (U : X.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U) :
    completedRealizationScalarSection e U (completedRealizationScalarInv e U a) = a := by
  exact congrArg (fun q ↦ q.hom.app U a) (completedRealizationScalarIso e).inv_hom_id

/-- The inverse underlying comparison with the original module's section type explicit.
Source: the given underlying comparison of a completed realization
(blueprint: lem-sfb-diagonal-completed-section-action). -/
def completedRealizationSectionInv {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) (M : DiagonalCompleted l X) (U : X.ProEtᵒᵖ)
    (m : M.val.obj U) : (e.F.obj M).X.obj.obj U :=
  (e.underlying.inv.app M).hom.app U m

private theorem scalarComparison_eq {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X)
    (c : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (hc : ∀ n : ℕ,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map c.inv ≫
          (purZlReduction l X (n + 1)).hom =
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            ((sheafCompose (Scheme.ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (Scheme.purTwistZlProjection X l n)) ≫
          (sfbConstantRingAbIso X
            (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom) :
    (completedRealizationScalarIso e).hom =
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map c.inv := by
  let J := Scheme.ProEt.topology X
  let W := sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let V := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙ W
  let : PreservesLimitsOfShape ℕᵒᵖ V := by
    let : PreservesLimitsOfShape ℕᵒᵖ (V ⋙ sheafToPresheaf J Ab.{u + 1}) := by
      change PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf J CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1}))
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves V
      (sheafToPresheaf J Ab.{u + 1})
  have hlim := isLimitOfPreserves V (limit.isLimit (Scheme.purTwistZlTower X l))
  apply (cancel_mono (W.map c.hom)).1
  rw [← W.map_comp, c.inv_hom_id, W.map_id]
  apply hlim.hom_ext
  intro n
  let q := W.map ((sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (Scheme.purTwistZlProjection X l n.unop))
  let k := (sfbConstantRingAbIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))))).hom
  have hq : W.map c.hom ≫ q ≫ k = (purZlReduction l X (n.unop + 1)).hom := by
    calc
      W.map c.hom ≫ q ≫ k =
          W.map c.hom ≫ (W.map c.inv ≫ (purZlReduction l X (n.unop + 1)).hom) :=
        congrArg (fun f ↦ W.map c.hom ≫ f) (hc n.unop).symm
      _ = _ := by
        rw [← Category.assoc, ← W.map_comp, c.hom_inv_id, W.map_id, Category.id_comp]
  change ((completedRealizationScalarIso e).hom ≫ W.map c.hom) ≫ q = (𝟙 _) ≫ q
  apply (cancel_mono k).1
  have he := eq_of_heq (e.unit_normalization n.unop)
  change (completedRealizationScalarIso e).hom ≫
    (purZlReduction l X (n.unop + 1)).hom = q ≫ k at he
  rw [← hq] at he
  simpa only [Category.assoc, Category.id_comp] using he

private theorem freeGenerator_action (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (e : CompletedRealization l X) (U : X.ProEtᵒᵖ)
    (hU : proAffineEtale U.unop.hom)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U) :
    coefficientSectionAction (e.F.obj (completedFreeCell l X U)) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app (completedFreeCell l X U)).hom.app U
          (completedFreeGenerator l X U)) =
      (e.underlying.inv.app (completedFreeCell l X U)).hom.app U
        (a • completedFreeGenerator l X U) := by
  obtain ⟨c, hc, _⟩ := completedCoefficientRingComparison_existsUnique l X
  have hb := scalarComparison_eq e c hc
  let P := completedFreeCell l X U
  let R := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X
  let N := (InternalAbelianSheafModule.sectionModuleFunctor
    (Scheme.ProEt.topology X) R).obj (e.F.obj P)
  have ha : c.hom.hom.app U (completedRealizationScalarSection e U a) = a := by
    change c.hom.hom.app U ((completedRealizationScalarIso e).hom.hom.app U a) = a
    rw [hb]
    exact congrArg (fun f ↦ f.hom.app U a) c.inv_hom_id
  have hz : (e.underlying.hom.app P).hom.app U
      ((e.underlying.inv.app P).hom.app U (completedFreeGenerator l X U)) =
        completedFreeGenerator l X U :=
    congrArg (fun f ↦ f.hom.app U (completedFreeGenerator l X U))
      (e.underlying.app P).inv_hom_id
  have h := completedFreeCell_automaticLinearity l X U hU c N
    (e.underlying.hom.app P) U (completedRealizationScalarSection e U a)
      ((e.underlying.inv.app P).hom.app U (completedFreeGenerator l X U))
  change (e.underlying.hom.app P).hom.app U
      (coefficientSectionAction (e.F.obj P) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app P).hom.app U (completedFreeGenerator l X U))) =
    @SMul.smul _ (P.val.obj U) inferInstance
      (c.hom.hom.app U (completedRealizationScalarSection e U a))
      ((e.underlying.hom.app P).hom.app U
        ((e.underlying.inv.app P).hom.app U (completedFreeGenerator l X U))) at h
  rw [ha, hz] at h
  have hi (x : (e.F.obj P).X.obj.obj U) :
      (e.underlying.inv.app P).hom.app U ((e.underlying.hom.app P).hom.app U x) = x :=
    congrArg (fun f ↦ f.hom.app U x) (e.underlying.app P).hom_inv_id
  have h' := congrArg (fun x ↦ (e.underlying.inv.app P).hom.app U x) h
  rw [hi] at h'
  exact h'

private theorem section_action_of_proAffineEtale (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (e : CompletedRealization l X) (M : DiagonalCompleted l X)
    (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U)
    (m : M.val.obj U) :
    coefficientSectionAction (e.F.obj M) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app M).hom.app U m) =
      (e.underlying.inv.app M).hom.app U (a • m) := by
  let P := completedFreeCell l X U
  let z := completedFreeGenerator l X U
  let g := completedFreeDesc M U m
  have hg : g.val.app U z = m := completedFreeDesc_generator M U m
  have hn (x : P.val.obj U) :
      (e.F.map g).hom.hom.app U ((e.underlying.inv.app P).hom.app U x) =
        (e.underlying.inv.app M).hom.app U (g.val.app U x) := by
    have h := congrArg (fun f ↦ f.hom.app U x) (e.underlying.inv.naturality g)
    exact h.symm
  have h := congrArg (fun x ↦ (e.F.map g).hom.hom.app U x)
    (freeGenerator_action l X e U hU a)
  change (e.F.map g).hom.hom.app U
      (CategoryTheory.SheafModuleSection.action (e.F.obj P) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app P).hom.app U z)) =
    (e.F.map g).hom.hom.app U ((e.underlying.inv.app P).hom.app U (a • z)) at h
  have hz : (e.F.map g).hom.hom.app U ((e.underlying.inv.app P).hom.app U z) =
      (e.underlying.inv.app M).hom.app U m :=
    (hn z).trans (congrArg (fun x ↦ (e.underlying.inv.app M).hom.app U x) hg)
  calc
    coefficientSectionAction (e.F.obj M) U (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app M).hom.app U m) =
      CategoryTheory.SheafModuleSection.action (e.F.obj M) U
        (completedRealizationScalarSection e U a)
        ((e.F.map g).hom.hom.app U ((e.underlying.inv.app P).hom.app U z)) :=
      congrArg (CategoryTheory.SheafModuleSection.action (e.F.obj M) U
        (completedRealizationScalarSection e U a)) hz.symm
    _ = (e.F.map g).hom.hom.app U
        (CategoryTheory.SheafModuleSection.action (e.F.obj P) U
          (completedRealizationScalarSection e U a)
          ((e.underlying.inv.app P).hom.app U z)) :=
      (CategoryTheory.SheafModuleSection.map_action (e.F.map g) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app P).hom.app U z)).symm
    _ = (e.F.map g).hom.hom.app U
        ((e.underlying.inv.app P).hom.app U (a • z)) := h
    _ = (e.underlying.inv.app M).hom.app U (g.val.app U (a • z)) := hn (a • z)
    _ = (e.underlying.inv.app M).hom.app U (a • m) :=
      congrArg (fun x ↦ (e.underlying.inv.app M).hom.app U x)
        (((g.val.app U).hom.map_smul a z).trans (congrArg (fun x ↦ a • x) hg))

private theorem coefficientAction_restrict {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} (N : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U)
    (x : N.X.obj.obj U) :
    N.X.obj.map f (coefficientSectionAction N U a x) =
      coefficientSectionAction N V
        ((condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.map f a)
        (N.X.obj.map f x) := by
  exact ((InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).obj N).val.map_smul f a x

/-- At one site, a normalized completed realization identifies the scalar action on
sections. This asserts no direct-image comparison or isomorphism between functors.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), coefficient identification;
the local-free-module argument in lem-diagonal-completed-ordinary-square.
(blueprint: lem-sfb-diagonal-completed-section-action).

Proof: the unit normalization identifies the coefficient comparison after every finite
projection. These projections jointly detect equality on the completed coefficient sheaf.
Construct the free module on a universe-lifted local representable by module
sheafification. Reconstruct the section module of its realized internal module and
apply automatic linearity into this free target to the underlying comparison.
Cancel that isomorphism to get the action identity on the distinguished generator.
The free/Yoneda/sheafification adjunctions construct a linear map sending this
generator to the specified section of any module. Apply the realization functor to
that map and use its internal linearity and naturality of the underlying comparison.
This first proves the identity over pro-affine etale objects. They form a
cover-dense basis of the pro-etale site. Restrict both sides along this basis, use
naturality of the action, coefficient comparison and underlying comparison, and
apply sheaf separatedness. Thus the identity holds on every pro-etale object. -/
theorem completedRealization_section_action (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (e : CompletedRealization l X) (M : DiagonalCompleted l X)
    (U : X.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U)
    (m : M.val.obj U) :
    coefficientSectionAction (e.F.obj M) U
        (completedRealizationScalarSection e U a)
        ((e.underlying.inv.app M).hom.app U m) =
      (e.underlying.inv.app M).hom.app U (a • m) := by
  let F := (e.F.obj M).X
  let lhs := coefficientSectionAction (e.F.obj M) U
    (completedRealizationScalarSection e U a) ((e.underlying.inv.app M).hom.app U m)
  let rhs := (e.underlying.inv.app M).hom.app U (a • m)
  let S := Presheaf.equalizerSieve (F := F.obj) lhs rhs
  have hS : S ∈ Scheme.ProEt.topology X U.unop := by
    let G := Scheme.AffineProEt.toProEt X
    refine (Scheme.ProEt.topology X).superset_covering ?_
      (G.is_cover_of_isCoverDense (Scheme.ProEt.topology X) U.unop)
    rintro Z g ⟨⟨W, i, f, hif⟩⟩
    have hf : S f := by
      change F.obj.map f.op lhs = F.obj.map f.op rhs
      dsimp only [lhs, rhs, F]
      have hs :
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.map f.op
              (completedRealizationScalarSection e U a) =
            completedRealizationScalarSection e (op (G.obj W))
              ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.op a) :=
        (NatTrans.naturality_apply (completedRealizationScalarIso e).hom.hom f.op a).symm
      have hm (z : M.val.obj U) :
          (e.F.obj M).X.obj.map f.op ((e.underlying.inv.app M).hom.app U z) =
            (e.underlying.inv.app M).hom.app (op (G.obj W)) (M.val.map f.op z) :=
        (NatTrans.naturality_apply (e.underlying.inv.app M).hom f.op z).symm
      rw [coefficientAction_restrict, hs, hm, hm, M.val.map_smul]
      exact section_action_of_proAffineEtale l X e M (op (G.obj W)) W.prop
        ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.op a)
        (M.val.map f.op m)
    rw [← hif]
    exact S.downward_closed hf i
  exact F.isSeparated U.unop S hS lhs rhs (fun _ _ hf ↦ hf)

/-- The single-site action identity with the original section types explicit.
Source: completedRealization_section_action
(blueprint: lem-sfb-diagonal-completed-section-action).
Proof: apply the single-site action identity; the section inverse is the same map. -/
theorem completedRealization_section_action_typed (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (e : CompletedRealization l X) (M : DiagonalCompleted l X)
    (U : X.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U)
    (m : M.val.obj U) :
    coefficientSectionAction (e.F.obj M) U
        (completedRealizationScalarSection e U a)
        (completedRealizationSectionInv e M U m) =
      completedRealizationSectionInv e M U (a • m) := by
  exact completedRealization_section_action l X e M U a m

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
