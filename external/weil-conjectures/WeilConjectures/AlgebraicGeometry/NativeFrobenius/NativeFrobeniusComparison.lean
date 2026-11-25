/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomComparison
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusSectionTransport
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusEvaluationCalculus

/-! # Native pullback versus translation on the fixed ordinary model

## References

* Stacks 03D6 and 03EO
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open CategoryTheory.TwistedActionRingedSite
open WeilConjectures.WeilFrobeniusAction
namespace AlgebraicGeometry.ProEtale.NativeFrobenius

private theorem native_iso_hom_inv {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N : AdicSheaf l Y} (e : M ≅ N) (V : Y.ProEtᵒᵖ) (z : M.X.obj.obj V) :
    e.inv.hom.hom.app V (e.hom.hom.hom.app V z) = z := by
  exact ConcreteCategory.congr_hom
    (congr_app (congrArg (fun k ↦ k.hom.hom) e.hom_inv_id) V) z

private theorem native_iso_inv_hom {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N : AdicSheaf l Y} (e : M ≅ N) (V : Y.ProEtᵒᵖ) (z : N.X.obj.obj V) :
    e.hom.hom.hom.app V (e.inv.hom.hom.app V z) = z := by
  exact native_iso_hom_inv e.symm V z

private theorem sectionCounit_injective (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (M : Modules (ring Y l)) (V : Y.ProEtᵒᵖ) :
    Function.Injective (((sectionCounit Y l).hom.app M).val.app V) := by
  intro a b h
  have h' := congrArg (((sectionCounit Y l).inv.app M).val.app V) h
  have hi (z) := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app V) ((sectionCounit Y l).app M).hom_inv_id) z
  exact (hi a).symm.trans (h'.trans (hi b))

-- Use the evaluation API without unfolding the chosen Hom map or counit.
attribute [local irreducible] homComparison sectionCounit

/-- For the *specified* lifted native coefficient model and its *specified* ordinary
Hom comparison, native pushforward by an inverse scheme isomorphism is translation,
compatibly with internal Hom. No site, ring, module equivalence, or Hom isomorphism
is chosen by this statement: all of those have already been constructed. -/
theorem nativeFrobeniusComparison (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (H : AdicModuleHomComparisonCore l Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    let E := equivalence Y l
    let S := sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)
    ∃ c : E.functor ⋙ adicLowerStar l g.inv ≅ S ⋙ E.functor,
      ∀ (P : Presentation (topology Y) (translation g) (ring Y l) (ringIso Y l g))
        (M N : Modules (ring Y l)),
      (adicLowerStar l g.inv).map (homComparison Y l H M N).hom ≫
          (adicLowerStarCompIhomIso l g.inv (E.functor.obj M)).inv.app (E.functor.obj N) ≫
          (Mod.ihomMap (c.app M).inv).app _ ≫
            (AdicSheaf.ihom (E.functor.obj (S.obj M))).map (c.app N).hom =
        c.hom.app (SheafOfModules.homObj (R := ring Y l) M N) ≫
          E.functor.map (P.sigmaHom M N).hom ≫
            (homComparison Y l H (S.obj M) (S.obj N)).hom := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  obtain ⟨c, hcs⟩ := nativeFrobeniusSectionTransport Y l g
  refine ⟨c, ?_⟩
  intro P M N
  let E := (equivalence Y l).functor
  let S := sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)
  let A := E.obj M
  let B := E.obj N
  let A' := E.obj (S.obj M)
  let B' := E.obj (S.obj N)
  let D := adicLowerStar l g.inv
  let h : E.obj (SheafOfModules.homObj (R := ring Y l) M N) ⟶
      (AdicSheaf.ihom A).obj B := (homComparison Y l H M N).hom
  let h' : E.obj (SheafOfModules.homObj (R := ring Y l) (S.obj M) (S.obj N)) ⟶
      (AdicSheaf.ihom A').obj B' := (homComparison Y l H (S.obj M) (S.obj N)).hom
  let eM : D.obj A ≅ A' := c.app M
  let eN : D.obj B ≅ B' := c.app N
  change D.map h ≫ (adicLowerStarCompIhomIso l g.inv A).inv.app B ≫
      (Mod.ihomMap eM.inv).app _ ≫ (AdicSheaf.ihom A').map eN.hom =
    c.hom.app (SheafOfModules.homObj (R := ring Y l) M N) ≫
      E.map (P.sigmaHom M N).hom ≫ h'
  apply evaluation_ext
  intro V z x
  let y := eM.inv.hom.hom.app V x
  have hx : eM.hom.hom.hom.app V y = x := native_iso_inv_hom eM V x
  rw [← hx]
  simp only [Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ModuleCat.comp_apply]
  erw [evaluation_map_target A' eN.hom,
    evaluation_map_source eM.inv (D.obj B), native_iso_hom_inv eM,
    pushforward_evaluation Y l g A B]
  apply sectionCounit_injective Y l (S.obj N) V
  erw [hcs N V,
    evaluation_restriction A B ((pullbackPostcomposeIso Y g).inv.app V.unop).op]
  simp only [D, adicLowerStar_map_hom]
  erw [lowerStar_map_hom_app (WeilCoefficients.{u} l) g.inv h.hom V.unop]
  have hn := ConcreteCategory.congr_hom
    (h.hom.hom.naturality ((pullbackPostcomposeIso Y g).inv.app V.unop).op) z
  simp only [ModuleCat.comp_apply] at hn
  erw [← hn]
  erw [comparison_evaluation Y l H M N
      (V := op ((postcompose g).functor.obj V.unop)),
    comparison_evaluation Y l H (S.obj M) (S.obj N) (V := V)]
  have hp := congrArg (fun k ↦ k.val.app V
    (((c.app (SheafOfModules.homObj (R := ring Y l) M N)).hom).hom.hom.app V z))
      ((sectionCounit Y l).hom.naturality (P.sigmaHom M N).hom)
  change ((sectionCounit Y l).hom.app
      (SheafOfModules.homObj (R := ring Y l) (S.obj M) (S.obj N))).val.app V
        ((E.map (P.sigmaHom M N).hom).hom.hom.app V
          ((c.app (SheafOfModules.homObj (R := ring Y l) M N)).hom.hom.hom.app V z)) =
    (P.sigmaHom M N).hom.val.app (op (AsSmall.up.obj V.unop))
      (((sectionCounit Y l).hom.app
        (S.obj (SheafOfModules.homObj (R := ring Y l) M N))).val.app V
          ((c.app (SheafOfModules.homObj (R := ring Y l) M N)).hom.hom.hom.app V z)) at hp
  -- Transport the local map and its argument separately to avoid rewriting the evaluation goal.
  have hf := hp.trans (congrArg ((P.sigmaHom M N).hom.val.app _)
    (hcs (SheafOfModules.homObj (R := ring Y l) M N) V z))
  exact (translated_evaluation Y l g P M N (op (AsSmall.up.obj V.unop)) _ _).symm.trans
    (congrArg₂ (fun (f : (SheafOfModules.homObj (R := ring Y l)
        (S.obj M) (S.obj N)).val.obj (op (AsSmall.up.obj V.unop)))
      (w : (S.obj M).val.obj (op (AsSmall.up.obj V.unop))) ↦
        f.app (op (Over.mk (𝟙 (AsSmall.up.obj V.unop)))) w)
      hf.symm (hcs M V y).symm)

end AlgebraicGeometry.ProEtale.NativeFrobenius
