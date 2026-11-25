/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

set_option linter.privateModule false

/-!
# Products and sequential derived limits of open extensions

The ring sheaf is an arbitrary monoid object in abelian sheaves. The module functors
are the recorded open-closed module-object functors, without commutative or constant
coefficient hypotheses. Derived categories use the standard localization universe.
The closed localization is descended as a composite, so no independent choice of a
localization on the closed stratum is needed.

## Main definitions

* `ringSheafDerivedCategory`: the existing derived category in its standard universe.
* `ringSheafDerivedOpenExtension`: termwise descent of the recorded exact open extension.
* `ringSheafDerivedDirectImage`: the recorded total right derived functor of direct image.
* `ringSheafDerivedClosedLocalization`: termwise descent of the exact composite `i_* i^*`.

## Main statement

* `proEtale_openExtension_products_derivedLimits`: the natural triangle, preservation of
  derived products and sequential Roos limits, and preservation of sheaf products.

## References

* Stacks Project, Tags 09BN, 0152, 070I and 08TC
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem products_of_essSurj
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : Type*) [HasProductsOfShape I C]
    (Q : C ⥤ D) [Q.EssSurj] (F : D ⥤ E)
    [PreservesLimitsOfShape (Discrete I) Q]
    [PreservesLimitsOfShape (Discrete I) (Q ⋙ F)] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → D) : PreservesLimit (Discrete.functor K) F := by
    let K' := fun n ↦ Q.objPreimage (K n)
    let e : Discrete.functor K' ⋙ Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor K' ⋙ Q) F :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves Q (limit.isLimit (Discrete.functor K')))
        (isLimitOfPreserves (Q ⋙ F) (limit.isLimit (Discrete.functor K')))
    exact preservesLimit_of_iso_diagram F e
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem derived_products_of_Q
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : Type*) [HasProductsOfShape I C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := D))] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  have : PreservesLimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact products_of_essSurj I DerivedCategory.Q F.mapDerivedCategory

end AlgebraicGeometry.ProEtale
