/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArbitraryFieldExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! Canonical constant-complex models for derived coefficient extension.
Source: Zheng, Construction 2.26 (blueprint: lem-sfb-ordinary-exceptional-change-of-rings).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The coefficient complex B[0] with its restricted A action.
Source: Zheng, Construction 2.26
(blueprint: def-sfb-ordinary-exceptional-scalar-tensor-data). -/
def ordinaryCoefficientComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : DerivedCategory (ModuleCat.{u + 1} A) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))

/-- Identify the restricted coefficient sheaf with the constant coefficient complex.
Source: constant sheaf commutes with scalar restriction and the degree-zero embedding
(blueprint: def-sfb-ordinary-exceptional-scalar-tensor-data). -/
def ordinaryScalarCoefficientIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarCoefficient φ T ≅ (constantFunctor A T).obj (ordinaryCoefficientComplex φ) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantCommuteCompose T.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
        (ModuleCat.of B B)) ≪≫
    ((Functor.mapDerivedCategorySingleFunctor
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).app _).symm

/-- Scalar extension followed by restriction is left tensor with B[0].
Source: the canonical scalar tensor comparison and derived tensor symmetry
(blueprint: def-sfb-ordinary-exceptional-scalar-tensor-data). -/
def ordinaryScalarTensorIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtension φ T ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ≅
      (derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((constantFunctor A T).obj (ordinaryCoefficientComplex φ)) :=
  scalarTensorIso φ T ≪≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).app (scalarCoefficient φ T)).symm ≪≫
    (derivedTensor (ModuleCat.{u + 1} A) T).mapIso (ordinaryScalarCoefficientIso φ T)

/-- The scalar-coefficient version of the ordered proper projection map.
Source: the projection clause of properFiniteCoefficientExtension
(blueprint: def-sfb-ordinary-exceptional-scalar-tensor-data). -/
def ordinaryScalarProjectionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj (scalarCoefficient φ Y)).obj
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K) ⟶
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj (scalarCoefficient φ Z)).obj K) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
      (scalarCoefficient φ Y)).app _ ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).app
      (scalarCoefficient φ Y) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      (((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
          (scalarCoefficientPullbackIso φ p).hom ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app
          (scalarCoefficient φ Z))

private theorem genericTensorSymmetry_swap
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (K L : DerivedCategory C) :
    ((DerivedCategory.canonicalTensorSymmetry C).hom.app K).app L =
      ((DerivedCategory.canonicalTensorSymmetry C).inv.app L).app K := by
  let : SymmetricCategory (DerivedCategory C) := DerivedCategory.symmetricCategory C
  exact SymmetricCategory.braiding_swap_eq_inv_braiding L K

/-- Swapping the factors gives the inverse signed derived symmetry.
Source: symmetry of the signed cochain tensor product
(blueprint: def-sfb-ordinary-exceptional-scalar-tensor-data). -/
theorem ordinaryTensorSymmetry_swap
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K L : DerivedCategoryModule A T) :
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app L =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).inv.app L).app K := by
  exact genericTensorSymmetry_swap
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) K L

end AlgebraicGeometry.Etale
