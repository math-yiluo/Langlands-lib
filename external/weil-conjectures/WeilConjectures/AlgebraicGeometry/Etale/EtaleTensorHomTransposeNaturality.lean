/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels

/-! # Naturality of the derived tensor-Hom transpose

The unary adjunction version of first-variable naturality, for use without
unfolding the closed derived structure.
(blueprint: lem-coef-etale-tensor-hom-transpose-naturality) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.instMonoidalCategory
  _root_.DerivedCategory.commShift₂CurriedTensor

/-- Naturality of the derived tensor-Hom transpose in its first variable.
Source: Stacks Project, Tag 08J9 (`lemma-internal-hom`); Mathlib's parametrized
adjunction naturality. Proof: apply homEquiv_symm_naturality_one to the published
parametrized derived tensor-Hom adjunction.
(blueprint: lem-coef-etale-tensor-hom-transpose-naturality) -/
theorem etaleTensorHomTranspose_naturality
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u})
    (K L M P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (f : K ⟶ L) (g : P ⟶ ((derivedHom C X).obj (op L)).obj M) :
    ((derivedTensorHomAdjunction C (X := X) K).homEquiv _ _).symm
        (g ≫ ((derivedHom C X).flip.obj M).map f.op) =
      ((derivedTensor C X).map f).app P ≫
        ((derivedTensorHomAdjunction C (X := X) L).homEquiv _ _).symm g := by
  exact ParametrizedAdjunction.homEquiv_symm_naturality_one
    (derivedTensorHomAdjunction₂ C X) f g

end AlgebraicGeometry.Etale
