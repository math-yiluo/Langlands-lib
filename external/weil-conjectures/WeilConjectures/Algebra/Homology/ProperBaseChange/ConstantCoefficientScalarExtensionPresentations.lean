/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

/-! # Scalar extension in ringed and fixed-coefficient presentations

Source: Stacks Project, Tags 06YY and 08FZ
(blueprint: def-weil-pbc-constant-coefficient-scalar-extension).

The original interface is retained; its fixed-coefficient specialization uses the
existing module-sheaf localization, scalar adjunction and derived tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace SheafOfModules
/-- The same existing scalar adjunction on the original small pro-etale site.
Source: Stacks 06YY (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
abbrev constantCoefficientProEtaleScalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : AlgebraicGeometry.Scheme.{u}) :=
  @AlgebraicGeometry.ProEtale.pbcFixedScalarExtension.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (AlgebraicGeometry.Scheme.ProEt.topology X)
    A B inferInstance inferInstance φ
end SheafOfModules
