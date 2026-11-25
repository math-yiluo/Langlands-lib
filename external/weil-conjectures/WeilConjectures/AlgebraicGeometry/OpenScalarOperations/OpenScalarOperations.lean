/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

/-! # Constant-ring pro-etale scalar and open operations

All declarations live in the namespace `AlgebraicGeometry.ProEtale.OpenScalarOperations`,
so they do not clash with the withdrawn `OpenScalarExchange` attachment. The constant
coefficient ring map is the existing `Scheme.proEtaleConstantRingMap`

## References

* Stacks Project, Tags 06YY, 07A6, 07A4, 08FJ and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

namespace OpenScalarOperations

attribute [instance] Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

/-- Termwise restriction of scalars `Res_T: D(B_T) ⥤ D(A_T)`,
localized to the unbounded derived categories; it is exact. -/
noncomputable def scalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T B ⥤ Scheme.proEtaleDerivedCategory T A :=
  (Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

end OpenScalarOperations

end AlgebraicGeometry.ProEtale
