/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Named instances for coefficient sheaves on the pro-étale site

Every instance below is found by type class inference anyway. Naming them once keeps
their large synthesized proof terms out of the statements that use them: the kernel then
checks each proof here, instead of re-inferring the types of the expanded proofs in every
statement mentioning cochain tensor products of pro-étale sheaves. The first group is for
an abstract coefficient category, the second for finite-ring coefficients `Mod_A`; with
both available, a generic lemma instantiated at `Mod_A` and a statement elaborated
directly for `Mod_A` contain proof terms with syntactically equal types.
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.FiniteCoefficientInstances
open AlgebraicGeometry Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

instance (priority := high) hasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (Sheaf (ProEt.topology X) A) := inferInstance

instance (priority := high) monoidalPreadditive :
    MonoidalPreadditive (Sheaf (ProEt.topology X) A) := inferInstance

instance (priority := high) hasZeroObject :
    HasZeroObject (Sheaf (ProEt.topology X) A) :=
  inferInstance

instance (priority := high) hasColimitsOfShape_int :
    HasColimitsOfShape ℤ (Sheaf (ProEt.topology X) A) := inferInstance

instance (priority := high) hasExactColimitsOfShape_int :
    HasExactColimitsOfShape ℤ (Sheaf (ProEt.topology X) A) := inferInstance

instance (priority := high) curriedTensor_additive :
    (curriedTensor (Sheaf (ProEt.topology X) A)).Additive := inferInstance

instance (priority := high) curriedTensor_preservesZeroMorphisms :
    (curriedTensor (Sheaf (ProEt.topology X) A)).PreservesZeroMorphisms := inferInstance

instance (priority := high) curriedTensor_obj_preservesZeroMorphisms
    (X₁ : (Sheaf (ProEt.topology X) A)) :
    ((curriedTensor (Sheaf (ProEt.topology X) A)).obj X₁).PreservesZeroMorphisms :=
  inferInstance

instance (priority := high) tensorLeft_additive
    (X₁ : (Sheaf (ProEt.topology X) A)) : (tensorLeft X₁).Additive := inferInstance

instance (priority := high) curriedTensor_obj_preservesColimitsOfShape_int
    (X₁ : (Sheaf (ProEt.topology X) A)) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf (ProEt.topology X) A)).obj X₁) :=
  inferInstance

instance (priority := high) curriedTensor_flip_obj_preservesColimitsOfShape_int
    (X₁ : (Sheaf (ProEt.topology X) A)) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf (ProEt.topology X) A)).flip.obj X₁) :=
  inferInstance

instance (priority := high) curriedTensor_obj_preservesColimit_empty
    (X₁ : (Sheaf (ProEt.topology X) A)) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) A))
      ((curriedTensor (Sheaf (ProEt.topology X) A)).obj X₁) := inferInstance

instance (priority := high) tensorRight_preservesColimit_empty
    (X₂ : (Sheaf (ProEt.topology X) A)) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) A)) (tensorRight X₂) :=
  inferInstance

instance (priority := high) curriedTensor_flip_obj_preservesColimit_empty
    (X₂ : (Sheaf (ProEt.topology X) A)) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) A))
      ((curriedTensor (Sheaf (ProEt.topology X) A)).flip.obj X₂) := inferInstance

instance (priority := high) gradedHasTensor
    (X₁ X₂ : GradedObject ℤ (Sheaf (ProEt.topology X) A)) :
    GradedObject.HasTensor X₁ X₂ := inferInstance

instance (priority := high) gradedHasTensor₄ObjExt
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf (ProEt.topology X) A)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance

instance (priority := high) gradedHasGoodTensor₁₂Tensor
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf (ProEt.topology X) A)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance

instance (priority := high) gradedHasGoodTensorTensor₂₃
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf (ProEt.topology X) A)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance

instance (priority := high) hasMapBifunctor
    (P Q : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Sheaf (ProEt.topology X) A)) (.up ℤ) :=
  inferInstance

instance (priority := high) hasDerivedMonoidalCategory :
    DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) A) (ComplexShape.up ℤ)) :=
  inferInstance

variable {A} in
instance (priority := high) upperStar_preservesZeroMorphisms
    {U : Scheme.{u}} (j : U ⟶ X) :
    (j)^*[A].PreservesZeroMorphisms := inferInstance

variable {A} in
instance (priority := high) upperStar_preservesFiniteColimits
    {U : Scheme.{u}} (j : U ⟶ X) :
    PreservesFiniteColimits (j)^*[A] := inferInstance

variable {A} in
instance (priority := high) upperStar_preservesKFlatQuasiIso [ProEtale.UpperStarPreservesFlat A]
    {U : Scheme.{u}} (j : U ⟶ X) :
    (j)^*[A].PreservesKFlatQuasiIso := inferInstance

end General

section ModuleCatCoefficients

variable (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})

instance (priority := high) hasColimitsOfSize_moduleCat :
    HasColimitsOfSize.{0, 0} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) := inferInstance

instance (priority := high) monoidalPreadditive_moduleCat :
    MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) := inferInstance

instance (priority := high) hasZeroObject_moduleCat :
    HasZeroObject (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  inferInstance

instance (priority := high) hasColimitsOfShape_int_moduleCat :
    HasColimitsOfShape ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) := inferInstance

instance (priority := high) hasExactColimitsOfShape_int_moduleCat :
    HasExactColimitsOfShape ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) := inferInstance

instance (priority := high) curriedTensor_additive_moduleCat :
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).Additive := inferInstance

instance (priority := high) curriedTensor_preservesZeroMorphisms_moduleCat :
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).PreservesZeroMorphisms :=
  inferInstance

instance (priority := high) curriedTensor_obj_preservesZeroMorphisms_moduleCat
    (X₁ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    Functor.PreservesZeroMorphisms
      ((curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).obj X₁) :=
  inferInstance

instance (priority := high) tensorLeft_additive_moduleCat
    (X₁ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) : (tensorLeft X₁).Additive :=
  inferInstance

instance (priority := high) curriedTensor_obj_preservesColimitsOfShape_int_moduleCat
    (X₁ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).obj X₁) :=
  inferInstance

instance (priority := high) curriedTensor_flip_obj_preservesColimitsOfShape_int_moduleCat
    (X₁ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).flip.obj X₁) :=
  inferInstance

instance (priority := high) curriedTensor_obj_preservesColimit_empty_moduleCat
    (X₁ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
      ((curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).obj X₁) := inferInstance

instance (priority := high) tensorRight_preservesColimit_empty_moduleCat
    (X₂ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
      (tensorRight X₂) :=
  inferInstance

instance (priority := high) curriedTensor_flip_obj_preservesColimit_empty_moduleCat
    (X₂ : (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    PreservesColimit (Functor.empty.{0} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
      ((curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))).flip.obj X₂) :=
  inferInstance

instance (priority := high) gradedHasTensor_moduleCat
    (X₁ X₂ : GradedObject ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    GradedObject.HasTensor X₁ X₂ := inferInstance

instance (priority := high) gradedHasTensor₄ObjExt_moduleCat
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance

instance (priority := high) gradedHasGoodTensor₁₂Tensor_moduleCat
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance

instance (priority := high) gradedHasGoodTensorTensor₂₃_moduleCat
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance

instance (priority := high) hasMapBifunctor_moduleCat
    (P Q : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) (.up ℤ) :=
  inferInstance

instance (priority := high) hasDerivedMonoidalCategory_moduleCat :
    DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
        (ComplexShape.up ℤ)) :=
  inferInstance

variable {A} in
instance (priority := high) upperStar_preservesZeroMorphisms_moduleCat
    {U : Scheme.{u}} (j : U ⟶ X) :
    (j)^*[(ModuleCat.{u + 1} A)].PreservesZeroMorphisms := inferInstance

variable {A} in
instance (priority := high) upperStar_preservesFiniteColimits_moduleCat
    {U : Scheme.{u}} (j : U ⟶ X) :
    PreservesFiniteColimits (j)^*[(ModuleCat.{u + 1} A)] := inferInstance

variable {A} in
instance (priority := high) upperStar_preservesKFlatQuasiIso_moduleCat [Finite A]
    {U : Scheme.{u}} (j : U ⟶ X) :
    (j)^*[ModuleCat.{u + 1} A].PreservesKFlatQuasiIso := inferInstance

end ModuleCatCoefficients

end AlgebraicGeometry.ProEtale.FiniteCoefficientInstances
