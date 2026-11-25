/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import all WeilConjectures.SixFunctors.Finite.Scalar.Fixed.FiniteScalarFixedTensorPullbackNormalization
import all WeilConjectures.AlgebraicGeometry.SectionDerivedRepresentativeSquare

/-! # Computing the tensor pullback comparison on cochain representatives
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedTensorComparison

private theorem exactTensorComparison
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F.leftDerivedFunctor ≅ F.mapDerivedCategory)
    (hf : ∀ P : CochainComplex C ℤ, e.hom.app (DerivedCategory.Q.obj P) ≫
      F.mapDerivedCategoryFactors.hom.app P =
      F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P))
    (A B : CochainComplex C ℤ) :
    e.inv.app
        (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B) ≫
      (F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj A)).app
        (DerivedCategory.Q.obj B) ≫
      (e.hom.app (DerivedCategory.Q.obj A) ⊗ₘ
        e.hom.app (DerivedCategory.Q.obj B)) ≫
      (F.mapDerivedCategoryFactors.hom.app A ⊗ₘ F.mapDerivedCategoryFactors.hom.app B) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj B) =
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A B) ≫
      F.mapDerivedCategoryFactors.hom.app (A ⊗ B) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app A).app B) := by
  simp only [tensorHom_comp_tensorHom_assoc, hf]
  rw [ModuleRingedComparison.DerivedRepresentativeSquare.cochain_tensor_comparison F A B, ← hf]
  simp only [Category.assoc]
  erw [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]

-- Elaborating the two monoidal presentations requires the exact pullback instances.
/-- The specified derived tensor pullback comparison computes the termwise oplax
comparison after the canonical localization factors. -/
theorem finiteFreeScalar_tensorPull_computes (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    tensorPull Λ f (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj C) ≫
      (F.mapDerivedCategoryFactors.hom.app A ⊗ₘ F.mapDerivedCategoryFactors.hom.app C) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj C) =
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A C) ≫
      F.mapDerivedCategoryFactors.hom.app (A ⊗ C) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app A).app C) := by
  let F := CondensedRing.upperStar Λ.X f
  have : F.PreservesFlat := by
    let G := ProEtale.upperStar Ab.{u + 1} f
    let R := condensedRingObj Λ.X Y
    let ρ := (asIso (condensedPullbackHom Λ.X f)).inv
    have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ.X X) ρ
    let e : F ≅ Mod.mapModComap ρ :=
      Functor.isoWhiskerLeft (G.mapMod R)
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f))
    exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩
  delta tensorPull
  rw [ModuleRingedComparison.internalPullOplax_eq_canonical Λ.X f]
  let : F.OplaxMonoidal := (CondensedRing.monoidal_upperStar Λ.X f).toOplaxMonoidal
  let : F.Monoidal := CondensedRing.monoidal_upperStar Λ.X f
  dsimp only [scalarSixPull]
  simp only [Category.assoc]
  have hf (P : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app
          (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) := by
    exact WeilConjectures.exact_factors_eq_counit F P
  exact exactTensorComparison F
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f) hf A C

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
