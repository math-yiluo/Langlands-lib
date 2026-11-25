/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Derived scalar-extension counits and composition -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory MonObj Limits
namespace CategoryTheory.Mod
namespace CounitComposition

open KFlatScalarTower

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

variable {T : C} [MonObj T] [IsCommMonObj T]
  (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]
  (h : φ ≫ ψ = χ)

private def ordinaryAssociation :
    Mod.extendScalars φ ⋙ Mod.extendScalars ψ ≅ Mod.extendScalars χ :=
  (Mod.extendScalarsComp φ ψ).symm ≪≫ eqToIso (by congr 1)

private theorem association_transpose
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ D} {I : D ⥤ B}
    {L : A ⥤ D} {J : D ⥤ A}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ J) (e : I ⋙ G ≅ J)
    (X : A) (Y : D) (f : L.obj X ⟶ Y) :
    a.homEquiv X (I.obj Y)
      (b.homEquiv (F.obj X) Y
        ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app X ≫ f)) =
      c.homEquiv X Y f ≫ e.inv.app Y := by
  apply (cancel_mono (e.hom.app Y)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hc := congrFun (congrFun (Adjunction.comp_homEquiv a b) X) Y
  rw [← Equiv.trans_apply, ← hc]
  have he := Adjunction.homEquiv_ofNatIsoRight_apply (a.comp b) e
    ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app X ≫ f)
  apply he.symm.trans
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
private theorem ordinaryAssociation_transpose
    (P : CochainComplex (Mod C R) ℤ) :
    ((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv _ _
      (((Mod.extendRestrictAdjunction ψ).mapHomologicalComplex (.up ℤ)).homEquiv _ _
        ((Functor.mapHomologicalComplexCompIso
          (ordinaryAssociation φ ψ χ h) (.up ℤ)).hom.app P)) =
      ((Mod.extendRestrictAdjunction χ).mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app
          (((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P) := by
  subst χ
  have he : Mod.comapCongr (rfl : φ ≫ ψ = φ ≫ ψ) = Iso.refl _ := by
    apply Iso.ext
    ext M
    rfl
  simp only [ordinaryAssociation, ordinaryRestrictionComp, he, eqToIso_refl, Iso.trans_refl]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext i : 1
  simpa [Adjunction.homEquiv_unit, ordinaryAssociation, ordinaryRestrictionComp,
    Functor.mapHomologicalComplexCompIso, Functor.mapHomologicalComplex,
    Adjunction.mapHomologicalComplex,
    Adjunction.leftAdjointUniq_inv_app, Mod.extendScalarsComp,
    Category.assoc] using
    association_transpose (Mod.extendRestrictAdjunction φ)
      (Mod.extendRestrictAdjunction ψ) (Mod.extendRestrictAdjunction (φ ≫ ψ))
      (Mod.comapComp φ ψ).symm (P.X i) _ (𝟙 _)

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T] in
private theorem restriction_inv_factor (Z : CochainComplex (Mod C T) ℤ) :
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app Z) ≫
      (Mod.comap φ).mapDerivedCategoryFactors.inv.app
        (((Mod.comap ψ).mapHomologicalComplex (.up ℤ)).obj Z) ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.comap ψ).mapDerivedCategoryFactors.inv.app Z) =
    (Mod.comap χ).mapDerivedCategoryFactors.inv.app Z ≫
      (Mod.mapDerivedCategoryComapCompIso φ ψ χ h).inv.app (DerivedCategory.Q.obj Z) := by
  have hf := Functor.exactDerivedRestrictionComposition_inv_factors
    (Mod.comap ψ) (Mod.comap φ) (Mod.comap χ)
    (ordinaryRestrictionComp φ ψ χ h) Z
  change (Mod.comap φ).mapDerivedCategoryFactors.inv.app _ ≫
    (Mod.comap φ).mapDerivedCategory.map _ ≫
    (Mod.mapDerivedCategoryComapCompIso φ ψ χ h).hom.app _ = _ at hf
  have hh := congrArg (fun k ↦ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (ordinaryRestrictionComp φ ψ χ h) (.up ℤ)).inv.app Z) ≫
      k ≫ (Mod.mapDerivedCategoryComapCompIso φ ψ χ h).inv.app (DerivedCategory.Q.obj Z)) hf
  simp only [Category.assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id, ← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id_app,
    DerivedCategory.Q.map_id, Category.id_comp] at hh
  exact hh


omit [IsMonHom φ] in
private theorem computationCounit_app_eq {R' S' : C} [MonObj R'] [MonObj S']
    [IsCommMonObj R'] [IsCommMonObj S'] (φ' : R' ⟶ S') [IsMonHom φ']
    (P : CochainComplex (Mod C R') ℤ) :
    (computationCounit φ').app P = (Mod.extendScalars φ').leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  dsimp only [computationCounit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Functor.mapHomotopyCategoryFactors_hom_app]
  erw [show (DerivedCategory.quotientCompQhIso (Mod C R')).inv.app P = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    show (DerivedCategory.quotientCompQhIso (Mod C S')).hom.app
      (((extendScalars φ').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) = 𝟙 _ from rfl,
    Category.comp_id]

/-- The canonical derived association intertwines the three computation counits.
Source: Stacks Tags 06YY and 0FND; the normalized transpose calculation in
`lem-pe-internal-kflat-scalar-tower-realization`.
(blueprint: lem-pe-internal-scalar-extension-counit-composition).

Proof: apply the composite derived adjunction's Hom bijection. Adjoint uniqueness
identifies the transpose of its association with the direct unit and the inverse
restriction compositor. Transpose the other side successively for the two scalar
extensions. The normalized derived transpose on complexes replaces each computation
counit by the ordinary adjunction transpose and the exact restriction factorization.
The ordinary association is itself defined by adjoint uniqueness, so its double
transpose is the direct ordinary unit and the inverse ordinary restriction compositor.
The localization composition equation for exact restrictions identifies the two
answers. The Hom bijection is injective. No flatness is needed for this identity. -/
theorem derivedExtendScalars_comp_counit
    (P : CochainComplex (Mod C R) ℤ) :
    let α := (((Mod.derivedExtendMapDerivedCategoryAdjunction φ).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction ψ)).ofNatIsoRight
        (Mod.mapDerivedCategoryComapCompIso φ ψ χ h)).leftAdjointUniq
          (Mod.derivedExtendMapDerivedCategoryAdjunction χ)
    let α₀ := (Mod.extendScalarsComp φ ψ).symm ≪≫
      eqToIso (by congr 1 : Mod.extendScalars (φ ≫ ψ) = Mod.extendScalars χ)
    α.hom.app (DerivedCategory.Q.obj P) ≫
      cast (by rfl) ((Mod.extendScalars χ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (Mod.extendScalars ψ).leftDerivedFunctor.map
        (cast (by rfl) ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :
            (Mod.extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
              DerivedCategory.Q.obj
                (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      cast (by rfl) ((Mod.extendScalars ψ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P))) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso α₀ (.up ℤ)).hom.app P) := by
  simp only [cast_eq]
  let a := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let b := Mod.derivedExtendMapDerivedCategoryAdjunction ψ
  let c := Mod.derivedExtendMapDerivedCategoryAdjunction χ
  let e := Mod.mapDerivedCategoryComapCompIso φ ψ χ h
  let Pφ := ((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
  let Pχ := ((Mod.extendScalars χ).mapHomologicalComplex (.up ℤ)).obj P
  let t := (Functor.mapHomologicalComplexCompIso
    (ordinaryAssociation φ ψ χ h) (.up ℤ)).hom.app P
  suffices key : (((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app
      (DerivedCategory.Q.obj P) ≫ (computationCounit χ).app P =
    (Mod.extendScalars ψ).leftDerivedFunctor.map ((computationCounit φ).app P) ≫
      (computationCounit ψ).app Pφ ≫ DerivedCategory.Q.map t by
    simp only [computationCounit_app_eq] at key
    exact key
  apply (b.homEquiv _ _).injective
  apply (a.homEquiv _ _).injective
  rw [association_transpose a b c e]
  rw [b.homEquiv_naturality_left]
  erw [transpose_cochain ψ Pφ Pχ t]
  rw [← Category.assoc, a.homEquiv_naturality_right]
  erw [transpose_cochain φ P _]
  rw [ordinaryAssociation_transpose]
  simp only [DerivedCategory.Q.map_comp, Category.assoc]
  rw [restriction_inv_factor]
  have hu := transpose_cochain χ P Pχ (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id] at hu
  change c.homEquiv _ _ ((computationCounit χ).app P) = _ at hu
  rw [hu]
  exact Category.assoc _ _ _


end CounitComposition
end CategoryTheory.Mod
