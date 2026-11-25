/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization

/-! # Composition of finite compact-support scalar comparisons

## References

* Bhatt--Scholze, Sections 6.5 and 6.7
* Stacks Tags 03DI, 0D6E and 0D6J
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

omit [Finite A] [Finite B] [Finite C] in
/-- The sectionwise coefficient compositor is the identity on sections. -/
private theorem restriction_comp_apply (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((sfCoefficientRestrictionComp T φ ψ).hom.app M).val.app V x = x :=
  (pbcRestrictComp_exists _ _ _
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm).exists.choose_spec
      M V x

omit [Finite A] [Finite B] [Finite C] in
/-- Cancel the sectionwise coefficient compositor against its inverse. -/
private theorem restrictionComp_inv_apply (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((sfCoefficientRestrictionComp T φ ψ).inv.app M).val.app V x = x := by
  have he := congrArg (fun k :
      (proEtaleCoefficientRestrictScalars T (ψ.comp φ)).obj M ⟶
        (proEtaleCoefficientRestrictScalars T (ψ.comp φ)).obj M ↦ k.val.app V x)
    ((sfCoefficientRestrictionComp T φ ψ).inv_hom_id_app M)
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    restriction_comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using he

/-- The ordinary direct-image comparisons preserve sections by their normalization. -/
private theorem imageRestriction_apply {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) (M : proEtaleRingModules Z (proEtaleConstantRing Z B))
    (V : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange g).op.obj V)) :
    ((proEtaleCoefficientDirectImageComparison g φ).hom.app M).val.app V x = x := by
  exact (proEtaleCoefficientDirectImageComparison_existsUnique g φ).choose_spec.1 M V x

omit [Finite A] in
/-- Direct image acts on a morphism by evaluating it over the base change. -/
private theorem directImage_map_apply {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {M N : proEtaleRingModules Z (proEtaleConstantRing Z A)} (f : M ⟶ N)
    (V : Y.ProEtᵒᵖ) (x : ((proEtaleConstantModuleDirectImage g A).obj M).val.obj V) :
    ((proEtaleConstantModuleDirectImage g A).map f).val.app V x =
      f.val.app ((proEtaleBaseChange g).op.obj V) x := rfl

/-- The inverse direct-image comparisons paste by uniqueness of their derived unit
normalizations. -/
private theorem derivedImageRestriction_inv_comp {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) (ψ : B →+* C) :
    (sfDerivedImageRestriction g (ψ.comp φ)).symm =
      Functor.isoWhiskerLeft (proEtaleConstantDerivedDirectImage g C)
          (sfDerivedCoefficientRestrictionComp Y φ ψ).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sfDerivedImageRestriction g ψ).symm
          (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (proEtaleCoefficientRestrictScalars Z ψ).mapDerivedCategory
          (sfDerivedImageRestriction g φ).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sfDerivedCoefficientRestrictionComp Z φ ψ)
          (proEtaleConstantDerivedDirectImage g A) := by
  apply FiniteFreeDirectImage.rightTower
    (proEtaleConstantModuleDirectImage g A) (proEtaleConstantModuleDirectImage g B)
    (proEtaleConstantModuleDirectImage g C)
    (proEtaleCoefficientRestrictScalars Y φ) (proEtaleCoefficientRestrictScalars Y ψ)
    (proEtaleCoefficientRestrictScalars Y (ψ.comp φ))
    (proEtaleCoefficientRestrictScalars Z φ) (proEtaleCoefficientRestrictScalars Z ψ)
    (proEtaleCoefficientRestrictScalars Z (ψ.comp φ))
    (sfCoefficientRestrictionComp Y φ ψ) (sfCoefficientRestrictionComp Z φ ψ)
    (sfDerivedImageRestriction g φ).symm (sfDerivedImageRestriction g ψ).symm
    (sfDerivedImageRestriction g (ψ.comp φ)).symm
    (proEtaleCoefficientDirectImageComparison g φ)
    (proEtaleCoefficientDirectImageComparison g ψ)
    (proEtaleCoefficientDirectImageComparison g (ψ.comp φ))
  · intro P
    exact WeilConjectures.compactSupportScalarDirectNormalization g φ P
  · intro P
    exact WeilConjectures.compactSupportScalarDirectNormalization g ψ P
  · intro P
    exact WeilConjectures.compactSupportScalarDirectNormalization g (ψ.comp φ) P
  · intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [directImage_map_apply, restriction_comp_apply]
    change ((proEtaleCoefficientDirectImageComparison g φ).hom.app
      ((proEtaleCoefficientRestrictScalars Z ψ).obj M)).val.app V
        (((proEtaleCoefficientDirectImageComparison g ψ).hom.app M).val.app V
          (((sfCoefficientRestrictionComp Y φ ψ).inv.app
            ((proEtaleConstantModuleDirectImage g C).obj M)).val.app V x)) =
      ((proEtaleCoefficientDirectImageComparison g (ψ.comp φ)).hom.app M).val.app V x
    rw [restrictionComp_inv_apply, imageRestriction_apply, imageRestriction_apply,
      imageRestriction_apply]

/-- Invert the inverse comparison cocycle and cancel the source compositor. -/
private theorem derivedImageRestriction_comp {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) (ψ : B →+* C) (K : proEtaleDerivedCategory Z C) :
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app K) ≫
      (sfDerivedImageRestriction g (ψ.comp φ)).hom.app K =
    (sfDerivedImageRestriction g φ).hom.app
        ((proEtaleCoefficientRestrictScalars Z ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfDerivedImageRestriction g ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((proEtaleConstantDerivedDirectImage g C).obj K) := by
  have hi := congrArg (fun e ↦ e.inv.app K) (derivedImageRestriction_inv_comp g φ ψ)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id] at hi
  rw [hi]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The compact-support coefficient comparisons compose for composable ring maps.
The comparison in SfCompactSupportRestrictionData is the extension-by-zero comparison
followed by the ordinary derived direct-image comparison. -/
theorem sfCompactSupportRestriction_comp
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (φ : A →+* B) (ψ : B →+* C)
    (K : proEtaleDerivedCategory X C) :
    (sfAmbientCompactSupportCandidate A c).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
      (sfCompactSupportRestriction c (ψ.comp φ)).hom.app K =
    (sfCompactSupportRestriction c φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfCompactSupportRestriction c ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((sfAmbientCompactSupportCandidate C c).obj K) := by
  have ho := sfOpenRestriction_derived_comp c.i φ ψ K
  have hp := derivedImageRestriction_comp c.g φ ψ
    ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj K)
  have hn := (sfDerivedImageRestriction c.g φ).hom.naturality
    ((sfOpenRestrictionDerived c.i ψ).hom.app K)
  change (proEtaleConstantDerivedDirectImage c.g A).map
      ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K)) ≫
    (proEtaleConstantDerivedDirectImage c.g A).map
      ((sfOpenRestrictionDerived c.i (ψ.comp φ)).hom.app K) ≫
    (sfDerivedImageRestriction c.g (ψ.comp φ)).hom.app
      ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj K) =
    ((proEtaleConstantDerivedDirectImage c.g A).map
        ((sfOpenRestrictionDerived c.i φ).hom.app
          ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K)) ≫
      (sfDerivedImageRestriction c.g φ).hom.app
        ((sfIntrinsicExtensionByZero c.i B).mapDerivedCategory.obj
          ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K))) ≫
    (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
      ((proEtaleConstantDerivedDirectImage c.g B).map
          ((sfOpenRestrictionDerived c.i ψ).hom.app K) ≫
        (sfDerivedImageRestriction c.g ψ).hom.app
          ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj K)) ≫
    (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
      ((proEtaleConstantDerivedDirectImage c.g C).obj
        ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj K))
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, ho, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hp]
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]

end AlgebraicGeometry.Scheme
