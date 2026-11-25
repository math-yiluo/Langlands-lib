/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicNativeBidual
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleTensorComparisonCore
import WeilConjectures.Algebra.Homology.SiteTensorHom.SiteTensorHomEquiv
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Yoneda

/-! # Hom part of the normalized adic module comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The Hom, evaluation, and bidual part of the normalized comparison for the explicit
adic section equivalence. Source: Stacks 03EO and 0E8H
(blueprint: lem-sf-adic-module-hom-comparison-core). -/
structure AdicModuleHomComparisonCore (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  /-- The Hom comparison is natural in the target. -/
  homIso : ∀ M : AdicSheaf l X,
    AdicSheaf.ihom M ⋙ (comparisonModuleFunctor l X) ≅
      (comparisonModuleFunctor l X) ⋙ (SheafOfModules.homFunctor (comparisonRing l X)).obj
        (op ((comparisonModuleFunctor l X).obj M))
  /-- It is contravariantly natural in the source. -/
  hom_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M' ⟶ M) (g : N ⟶ N'),
    (comparisonModuleFunctor l X).map ((Mod.ihomMap f).app N ≫ (AdicSheaf.ihom M').map g) ≫
        (homIso M').hom.app N' =
      (homIso M).hom.app N ≫ SheafOfModules.homObjMap (R := comparisonRing l X)
        ((comparisonModuleFunctor l X).map f) ((comparisonModuleFunctor l X).map g)
  /-- Native evaluation is the slice map `(x, λ) ↦ λ(x)`. -/
  evaluation : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V),
    (AddEquiv.refl _) (adicComparisonEval M N V z x) =
      ((((homIso M).hom.app N).val.app V ((AddEquiv.refl _) z)).app
        (op (Over.mk (𝟙 V.unop)))) ((AddEquiv.refl _) x)
  /-- In slice coordinates the bidual sends `x` to `λ ↦ λ(x|_W)` on every further object. -/
  bidual_sections : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V)
    (W : Over V.unop)
    (z : ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X.obj.obj (op W.left)),
    (((homIso ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).hom.app
        (AdicSheaf.unit l X)).val.app V
      ((AddEquiv.refl _) ((adicNativeBidual M).hom.hom.app V x))).app (op W)
        ((AddEquiv.refl _) z) =
      (AddEquiv.refl _)
        (adicComparisonEval M (AdicSheaf.unit l X) (op W.left) z (M.X.obj.map W.hom.op x))

private noncomputable def sectionPair {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (V : X.ProEtᵒᵖ) (p : P.obj.obj V) (q : Q.obj.obj V) : (P ⊗ Q).obj.obj V :=
  (Sheaf.tensorObjComparison (Scheme.ProEt.topology X) P Q).app V
    (p ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] q)

private theorem sectionPair_map {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {P Q P' Q' : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (f : P ⟶ P') (g : Q ⟶ Q') (V : X.ProEtᵒᵖ)
    (p : P.obj.obj V) (q : Q.obj.obj V) :
    (f ⊗ₘ g).hom.app V (sectionPair P Q V p q) =
      sectionPair P' Q' V (f.hom.app V p) (g.hom.app V q) := by
  exact ConcreteCategory.congr_hom
    (congr_app (Sheaf.tensorObjComparison_naturality f g) V) (p ⊗ₜ[_] q)

private theorem sectionPair_braiding {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (V : X.ProEtᵒᵖ) (p : P.obj.obj V) (q : Q.obj.obj V) :
    (β_ P Q).hom.hom.app V (sectionPair P Q V p q) = sectionPair Q P V q p := by
  have h := Functor.LaxBraided.braided
    (F := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) P Q
  exact ConcreteCategory.congr_hom (congr_app h V) (p ⊗ₜ[_] q)

private theorem evaluation_map_source {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {M M' : AdicSheaf l X} (f : M' ⟶ M) (N : AdicSheaf l X)
    (V : X.ProEtᵒᵖ) (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (x : M'.X.obj.obj V) :
    adicComparisonEval M' N V (((Mod.ihomMap f).app N).hom.hom.app V z) x =
      adicComparisonEval M N V z (f.hom.hom.app V x) := by
  change (Mod.evaluation M' N).hom.app V
      (sectionPair ((AdicSheaf.ihom M').obj N).X M'.X V
        (((Mod.ihomMap f).app N).hom.hom.app V z) x) =
    (Mod.evaluation M N).hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z (f.hom.hom.app V x))
  have h := congrArg (fun k ↦ k.hom.app V
    (sectionPair ((AdicSheaf.ihom M).obj N).X M'.X V z x))
      (Mod.evaluation_ihomMap f N)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, ← id_tensorHom, sectionPair_map,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using h

private theorem evaluation_map_target {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) {N N' : AdicSheaf l X} (g : N ⟶ N')
    (V : X.ProEtᵒᵖ) (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (x : M.X.obj.obj V) :
    adicComparisonEval M N' V (((AdicSheaf.ihom M).map g).hom.hom.app V z) x =
      g.hom.hom.app V (adicComparisonEval M N V z x) := by
  change (Mod.evaluation M N').hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N').X M.X V
        (((AdicSheaf.ihom M).map g).hom.hom.app V z) x) =
    g.hom.hom.app V ((Mod.evaluation M N).hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z x))
  have h := congrArg (fun k ↦ k.hom.app V
    (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z x))
      (Mod.evaluation_naturality M g)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, sectionPair_map, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using h

private theorem evaluation_bidual {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V)
    (z : ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X.obj.obj V) :
    adicComparisonEval ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))
      (AdicSheaf.unit l X) V ((adicNativeBidual M).hom.hom.app V x) z =
        adicComparisonEval M (AdicSheaf.unit l X) V z x := by
  change (Mod.evaluation ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))
      (AdicSheaf.unit l X)).hom.app V
      (sectionPair _ _ V ((adicNativeBidual M).hom.hom.app V x) z) =
    (Mod.evaluation M (AdicSheaf.unit l X)).hom.app V (sectionPair _ _ V z x)
  have h := congrArg (fun k ↦ k.hom.app V
    (sectionPair M.X ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X V x z))
      (adicNativeBidual_transpose M)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, sectionPair_map, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply, sectionPair_braiding] using h

private noncomputable def homComparison {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (T : AdicModuleTensorComparisonCore l X) (M N : AdicSheaf l X) :
    (comparisonModuleFunctor l X).obj ((AdicSheaf.ihom M).obj N) ⟶
      SheafOfModules.homObj (R := comparisonRing l X) ((comparisonModuleFunctor l X).obj M)
        ((comparisonModuleFunctor l X).obj N) :=
  SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1} _ _ _
    ((T.tensorIso M).inv.app ((AdicSheaf.ihom M).obj N) ≫
      (comparisonModuleFunctor l X).map ((Mod.ihomAdjunction M).counit.app N))

private theorem homComparison_sections {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (T : AdicModuleTensorComparisonCore l X) (M N : AdicSheaf l X)
    (V : X.ProEtᵒᵖ) (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (W : Over V.unop) (x : M.X.obj.obj (op W.left)) :
    (((homComparison T M N).val.app V z).app (op W)) x =
      adicComparisonEval M N (op W.left)
        (((AdicSheaf.ihom M).obj N).X.obj.map W.hom.op z) x := by
  change ((T.tensorIso M).inv.app ((AdicSheaf.ihom M).obj N) ≫
    (comparisonModuleFunctor l X).map ((Mod.ihomAdjunction M).counit.app N)).val.app
      (op W.left) (SheafOfModules.siteSheafTensorTmul
        ((comparisonModuleFunctor l X).obj ((AdicSheaf.ihom M).obj N))
        ((comparisonModuleFunctor l X).obj M) (op W.left)
        (((AdicSheaf.ihom M).obj N).X.obj.map W.hom.op z) x) = _
  have h := T.tensor_sections ((AdicSheaf.ihom M).obj N) M (op W.left)
    (((AdicSheaf.ihom M).obj N).X.obj.map W.hom.op z) x
  change ((T.tensorIso M).hom.app _).val.app _ (adicComparisonTmul _ _ _ _ _) = _ at h
  simp only [AddEquiv.refl_apply] at h
  erw [← h]
  change ((comparisonModuleFunctor l X).map ((Mod.ihomAdjunction M).counit.app N)).val.app _
    ((((T.tensorIso M).hom.app _ ≫ (T.tensorIso M).inv.app _).val.app _)
      (adicComparisonTmul _ _ _ _ _)) = _
  rw [Iso.hom_inv_id_app]
  rfl

private theorem homComparison_naturality {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (T : AdicModuleTensorComparisonCore l X)
    {M M' N N' : AdicSheaf l X} (f : M' ⟶ M) (g : N ⟶ N') :
    (comparisonModuleFunctor l X).map
        ((Mod.ihomMap f).app N ≫ (AdicSheaf.ihom M').map g) ≫ homComparison T M' N' =
      homComparison T M N ≫ SheafOfModules.homObjMap (R := comparisonRing l X)
        ((comparisonModuleFunctor l X).map f) ((comparisonModuleFunctor l X).map g) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((homComparison T M' N').val.app V
    (((Mod.ihomMap f).app N ≫ (AdicSheaf.ihom M').map g).hom.hom.app V z)).app W) x = _
  rw [homComparison_sections]
  rw [← NatTrans.naturality_apply]
  change adicComparisonEval M' N' _
    (((AdicSheaf.ihom M').map g).hom.hom.app _
      (((Mod.ihomMap f).app N).hom.hom.app _
        (((AdicSheaf.ihom M).obj N).X.obj.map W.unop.hom.op z))) x = _
  rw [evaluation_map_target, evaluation_map_source]
  change _ = g.hom.hom.app _ ((((homComparison T M N).val.app V z).app W)
    (f.hom.hom.app _ x))
  rw [homComparison_sections]
  rfl

private theorem homComparison_isIso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (T : AdicModuleTensorComparisonCore l X) (M N : AdicSheaf l X) :
    IsIso (homComparison T M N) := by
  let F := comparisonModuleFunctor l X
  let FF := comparisonModuleFullyFaithful l X
  let e (P : AdicSheaf l X) :
      (P ⟶ (AdicSheaf.ihom M).obj N) ≃
        (F.obj P ⟶ SheafOfModules.homObj (R := comparisonRing l X) (F.obj M) (F.obj N)) :=
    ((((Mod.ihomAdjunction M).homEquiv P N).symm.trans FF.homEquiv).trans
      (((T.tensorIso M).app P).homCongr (Iso.refl _))).trans
        (SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1}
          (F.obj P) (F.obj M) (F.obj N))
  have he (P : AdicSheaf l X) (h : P ⟶ (AdicSheaf.ihom M).obj N) :
      e P h = F.map h ≫ homComparison T M N := by
    change SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1} _ _ _
      ((T.tensorIso M).inv.app P ≫
        F.map (((Mod.ihomAdjunction M).homEquiv P N).symm h)) = _
    rw [Adjunction.homEquiv_counit, F.map_comp]
    have hn := (T.tensorIso M).inv.naturality h
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc]
    exact SheafOfModules.SiteTensorHom.equiv_naturality (F.map h) _
  apply isIso_of_yoneda_map_bijective
  intro Q
  let i := F.objObjPreimageIso Q
  let eQ : (Q ⟶ F.obj ((AdicSheaf.ihom M).obj N)) ≃
      (Q ⟶ SheafOfModules.homObj (R := comparisonRing l X) (F.obj M) (F.obj N)) :=
    ((i.homCongr (Iso.refl _)).symm.trans FF.homEquiv.symm).trans
      ((e (F.objPreimage Q)).trans (i.homCongr (Iso.refl _)))
  convert eQ.bijective using 1
  funext h
  change (h ≫ homComparison T M N) =
    i.inv ≫ e (F.objPreimage Q) (FF.preimage (i.hom ≫ h)) ≫ 𝟙 _
  rw [he, Category.comp_id, FF.map_preimage, ← Category.assoc, Iso.inv_hom_id_assoc]

/-- The normalized Hom comparison and its evaluation and bidual formulas exist for every
prime and scheme.

Proof: curry the image of native evaluation through the normalized tensor comparison.
The native tensor-Hom adjunction, full faithfulness, and sheaf currying give bijections
on Hom sets; essential surjectivity and Yoneda prove that the comparison is invertible.
Its pure-tensor formula gives evaluation and naturality. The braided transpose identity
for the native bidual gives the bidual formula after restriction.
Source: Stacks 03EO and 0E8H
(blueprint: lem-sf-adic-module-hom-comparison-core). -/
theorem adicModuleHomComparisonCore (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (AdicModuleHomComparisonCore l X) := by
  obtain ⟨T⟩ := adicModuleTensorComparisonCore l X
  let H (M : AdicSheaf l X) :
      AdicSheaf.ihom M ⋙ (comparisonModuleFunctor l X) ≅
        (comparisonModuleFunctor l X) ⋙
          (SheafOfModules.homFunctor (comparisonRing l X)).obj
            (op ((comparisonModuleFunctor l X).obj M)) :=
    NatIso.ofComponents (fun N ↦ by
      letI := homComparison_isIso T M N
      exact asIso (homComparison T M N)) (fun g ↦ by
        change (comparisonModuleFunctor l X).map ((AdicSheaf.ihom M).map g) ≫
            homComparison T M _ =
          homComparison T M _ ≫ SheafOfModules.homObjMap (R := comparisonRing l X)
            (𝟙 _) ((comparisonModuleFunctor l X).map g)
        simpa only [Mod.ihomMap_id, NatTrans.id_app, Category.id_comp,
          CategoryTheory.Functor.map_id] using
          homComparison_naturality T (𝟙 M) g)
  refine ⟨{ homIso := H
            hom_naturality := fun f g ↦ homComparison_naturality T f g
            evaluation := ?_
            bidual_sections := ?_ }⟩
  · intro M N V z x
    change adicComparisonEval M N V z x =
      (((homComparison T M N).val.app V z).app (op (Over.mk (𝟙 V.unop)))) x
    rw [homComparison_sections]
    change adicComparisonEval M N V z x =
      adicComparisonEval M N V (((AdicSheaf.ihom M).obj N).X.obj.map (𝟙 V) z) x
    rw [CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  · intro M V x W z
    change (((homComparison T ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))
      (AdicSheaf.unit l X)).val.app V ((adicNativeBidual M).hom.hom.app V x)).app (op W)) z = _
    rw [homComparison_sections, ← NatTrans.naturality_apply, evaluation_bidual]
    rfl

end AlgebraicGeometry.ProEtale
