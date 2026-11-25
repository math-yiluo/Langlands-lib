/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityData

/-! # Data for tensor compatibility of degree-zero etale sheaves

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU.
(blueprint: def-pur-etale-flat-single-tensor-compatibility-data).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X X' : AlgebraicGeometry.Scheme.{u}}

/-- Map a pair of arrows with the specified derived tensor bifunctor.
Source: Stacks Tag 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The coefficient category stays abstract when this composite is checked. -/
noncomputable def derivedTensorPairMap (X : AlgebraicGeometry.Scheme.{u})
    {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g

end AlgebraicGeometry.Etale
