/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseLocalizationMap
import WeilConjectures.Algebra.Homology.LocalizationRestrictionKFlat
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # B-linear invertibility of base localization

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-is-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R Rp B A D : Type u)
  [CommRing R] [CommRing Rp] [CommRing B] [CommRing A] [CommRing D]
  [Algebra R Rp] [Algebra R B] [Algebra Rp B] [IsScalarTower R Rp B]
  [Algebra R A] [Algebra Rp A] [IsScalarTower R Rp A]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The canonical base-localization map is an isomorphism on B-linear cohomology.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-is-iso).

Proof: choose a K-flat Rp-resolution P of the restricted input Q. Restriction to R
preserves K-flatness: tensor an acyclic R-complex with Rp, use exactness of localization,
and identify its tensor with P by associativity. Apply the K-flat counit theorem to
both universal derived functors on P. The counit equation for the universal lift,
and the ordinary localization tensor isomorphism, then make the lift on P invertible.
The augmentation P to Q is a quasi-isomorphism over both bases; naturality transports
invertibility to Q. Apply the B-homology functor and conjugate by the two model
cohomology isomorphisms. This is exactly baseLocalizationCohomologyMap. Identity
localization gives model transport; when S contains zero, both cohomologies are zero.
No algebra structures on D over A or B, and no flatness of D, are needed. -/
theorem baseLocalizationCohomologyMap_isIso
    (S : Submonoid R) [IsLocalization S Rp]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) (i : ℤ) :
    IsIso (baseLocalizationCohomologyMap R Rp B A D S Q L K i) := by
  classical
  have (T : Type u) [CommRing T] (N : ModuleCat.{u} T) :
      CategoryTheory.Limits.PreservesColimitsOfShape ℤ
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} T)).flip.obj N) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      (MonoidalCategory.tensorRight N))
  have (T : Type u) [CommRing T] :
      CategoryTheory.HasExactColimitsOfShape ℤ (ModuleCat.{u} T) :=
    CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} T)
      (AsSmall.equiv (C := ℤ)).symm
  have (T : Type u) [CommRing T] (f : T →+* B) :
      (ModuleCat.extendScalars f).PreservesKFlatQuasiIso :=
    ⟨fun hP hP' a ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat f a
      (show QuasiIso a from inferInstance) hP hP'⟩
  let r := ModuleCat.restrictScalars.{u} (algebraMap R Rp)
  have hε : (r.mapDerivedCategory ⋙ L.derived).IsLeftDerivedFunctor
      (baseLocalizationCounit R Rp B A D S Q L)
      (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) := by
    apply (Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat
      (ModuleCat.extendScalars (algebraMap Rp B)) _).2
    intro P hP
    have hPr := ModuleCat.kFlat_restrictScalars_of_isLocalization S P hP
    have hc := (Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat
      (ModuleCat.extendScalars (algebraMap R B)) L.counit).1 L.universal _ hPr
    dsimp only [baseLocalizationCounit]
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    have hc' : IsIso (L.counit.app
        ((r.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P))) := by
      exact (NatTrans.isIso_app_iff_of_iso L.counit
        ((r.mapHomotopyCategoryFactors (.up ℤ)).app P)).2 hc
    infer_instance
  let := K.universal
  have hη : IsIso (baseLocalizationDerivedMap R Rp B A D S Q L K) := by
    exact (K.derived.isLeftDerivedFunctor_iff_isIso_leftDerivedLift K.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) _ _).1 hε
  dsimp only [baseLocalizationCohomologyMap]
  infer_instance

end RingTensorCohomology
