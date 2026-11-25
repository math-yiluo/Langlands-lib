/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage

/-!
# Intrinsic constructibility in the fixed-coefficient presentation

This is the intrinsic finite-stratification definition in the fixed-module encoding
and in the coefficient universe required by the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite constructible locally closed stratification, local constancy on each
stratum, and finite geometric stalks. No bound, common stratification, or etale
origin is part of this sheaf predicate. -/
def IsConstructibleProEtaleFixedModuleSheaf (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : Prop :=
  ∃ S : Stratification Y, 0 < S.n ∧
    (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleFixedModuleSheaf (S.domain i) A
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricFixedModuleStalk y A
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F))

end AlgebraicGeometry.Scheme
