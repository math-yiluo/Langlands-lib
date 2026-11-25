/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective

/-! # Forgetting support of an étale finite antecedent -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u wC wD wH
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mk₀
  Ext.mapExactFunctor Ext.homEquiv

private theorem source_iso_cancel
    {C : Type*} [Category C] [Abelian C] [HasExt.{wC} C]
    {X X' P Q : C} (e : X ≅ X') (f : X' ⟶ P) (z : Ext.{wC} P Q 2)
    (v : Ext.{wC} X Q 2)
    (h : (Ext.mk₀ (e.hom ≫ f)).comp z (zero_add 2) = v) :
    (Ext.mk₀ f).comp z (zero_add 2) = (Ext.mk₀ e.inv).comp v (zero_add 2) := by
  rw [← h, Ext.mk₀_comp_mk₀_assoc]
  simp only [Iso.inv_hom_id_assoc]

private theorem exact_source_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{wC} C] [HasExt.{wD} D] [HasDerivedCategory.{wH} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X P Q : C} (f : X ⟶ P) (z : Ext.{wC} P Q 2) :
    (((Ext.mk₀ f).comp z (zero_add 2)).mapExactFunctor F).hom =
      (DerivedCategory.singleFunctor D 0).map (F.map f) ≫ (z.mapExactFunctor F).hom := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]

private theorem supported_image_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) (z : GeoCartierClass A N hA i)
    (b : Ext (Etale.ordinaryFiniteConstant A T)
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (h : (Ext.mk₀
      (((comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A))).comp z (zero_add 2) =
      b.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) T)) :
    (Ext.mk₀ (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A))).comp z (zero_add 2) = finiteEtaleProImage A T N hA b := by
  rw [finiteEtaleProImage_apply]
  unfold Ext.mk₀CompMk₀ finiteEtaleLineIso
  simp only [Iso.refl_hom, Ext.comp_mk₀_id]
  apply source_iso_cancel (finiteEtaleConstantIso A T)
  simpa only [finiteEtaleConstantIso] using h

/-- Forget support, apply any exact functor, and take the derived hom of an étale antecedent.
Source: the second equation of GeoCartierChernEquation and exact Ext functoriality.
(blueprint: lem-sfb-diagonal-trace-finite-supported-comparison).

Proof: precompose the geometric equation with the inverse constant comparison. Ext
associativity cancels that isomorphism and yields the canonical finiteEtaleProImage.
Apply the exact functor and take Ext hom; degree-zero composition becomes ordinary
composition with the single-functor image of the support-forgetting map. -/
theorem finiteSupportedComparison_hom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) (z : GeoCartierClass A N hA i)
    (b : Ext (Etale.ordinaryFiniteConstant A T)
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (h : (Ext.mk₀
      (((comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A))).comp z (zero_add 2) =
      b.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) T))
    {E : Type*} [Category E] [Abelian E] [HasExt.{wD} E]
    [HasDerivedCategory.{wH} E]
    (S : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ E)
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S] :
    (DerivedCategory.singleFunctor E 0).map
      (S.map (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
        (ModuleCat.of A A))) ≫ (z.mapExactFunctor S).hom =
      ((finiteEtaleProImage A T N hA b).mapExactFunctor S).hom := by
  have e := supported_image_eq A N hA i z b h
  have hh := congrArg (fun v ↦ (v.mapExactFunctor S).hom) e
  rw [exact_source_hom] at hh
  exact hh

end AlgebraicGeometry.ProEtale.DiagonalTrace
