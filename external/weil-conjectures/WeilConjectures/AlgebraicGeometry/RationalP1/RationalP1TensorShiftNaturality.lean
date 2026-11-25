/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection

/-! # Naturality of the rational tensor-shift comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] tensorShiftIso twist rationalTwistFunctor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private def TensorShiftFamily (X : Scheme.{u}) (L : Modules Λ X) :=
  ∀ A : DerivedCategory (Modules Λ X),
    A ⊗ (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) ≅
      (twist Λ X L).obj A

private def TensorShiftNormalized (X : Scheme.{u}) (L : Modules Λ X)
    (e : TensorShiftFamily Λ X L) : Prop :=
  ∀ A, HEq (e A) (((tensorLeft A).commShiftIso (2 : ℤ)).app
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L))

private def TensorShiftNatural (X : Scheme.{u}) (L : Modules Λ X)
    (e : TensorShiftFamily Λ X L) : Prop :=
  ∀ {A B : DerivedCategory (Modules Λ X)} (f : A ⟶ B),
    tensorHom f (𝟙 _) ≫ (e B).hom = (e A).hom ≫ (twist Λ X L).map f

attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem normalizedTensorShift_naturality (X : Scheme.{u}) (L : Modules Λ X)
    (e : TensorShiftFamily Λ X L) (he : TensorShiftNormalized Λ X L e) :
    TensorShiftNatural Λ X L e := by
  unfold TensorShiftNatural TensorShiftNormalized TensorShiftFamily
    internalTensorCommShift internalMonoidal internalTensorBundle nativeTensorBundle
    twist rationalTwistFunctor CondensedRing.derivedTensor at *
  intro A B f
  rw [eq_of_heq (he A), eq_of_heq (he B)]
  simpa only [Iso.app_hom, Functor.comp_obj, Functor.comp_map,
    Functor.flip_obj_obj, Functor.flip_obj_map, curriedTensor_obj_obj,
    curriedTensor_map_app, tensorHom_id, DerivedCategory.commShiftTensorLeft] using
    (NatTrans.shift_app_comm ((curriedTensor _).map f) (2 : ℤ)
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L)).symm

/-- Naturality of the fixed tensor-shift comparison in the module-object tensor interface. -/
theorem tensorShiftIso_naturality (X : Scheme.{u}) (L : Modules Λ X)
    {A B : DerivedCategory (Modules Λ X)} (f : A ⟶ B) :
    tensorHom f (𝟙 _) ≫ (tensorShiftIso Λ X L B).hom =
      (tensorShiftIso Λ X L A).hom ≫ (twist Λ X L).map f :=
  normalizedTensorShift_naturality Λ X L (tensorShiftIso Λ X L)
    (fun A ↦ by
      unfold tensorShiftIso
      exact (tensorShift_existsUnique Λ X L A).exists.choose_spec) f

end AlgebraicGeometry.ProEtale.RationalP1
