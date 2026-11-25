/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# Constant coefficient tensor comparison for an open immersion

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
lemma proposition-open-direct-image-preserves-finite (blueprint:
proposition-open-direct-image-preserves-finite).

The comparison is the existing unbounded projection-formula morphism at the constant
module sheaf in degree zero. Its target is identified with the tensor by the constant
module on the source through the canonical constant inverse-image isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ExceptionalConstantTensor

open CategoryTheory CategoryTheory.Limits

universe v

variable {R : Type v} [CommRing R]

section Devissage

variable {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : _root_.DerivedCategory (ModuleCat.{v} R) ⥤ D}
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

end Devissage

end ExceptionalConstantTensor

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
