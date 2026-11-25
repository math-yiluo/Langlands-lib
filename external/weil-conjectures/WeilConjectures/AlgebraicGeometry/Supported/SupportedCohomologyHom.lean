/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Supported.SupportedSectionsHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.R.RHomDerivedRoof

/-!
# Supported cohomology as morphisms

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-pur-supported-hom.md,
order 1940 (blueprint: lemma-sections-support-closed-subscheme--1).

The coefficient sheaf is pushed forward before being placed in degree zero.
The derived category is the ambient category of all module sheaves. The natural
isomorphism is between additive-group-valued functors on its bounded-below subcategory.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

private noncomputable def exactPostcompositionDerivedIso.{uC, uD, uE, vC, vD, vE, wC, wD, wE}
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasDerivedCategory.{wE} E]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus := by
  let e : (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G.mapDerivedCategoryPlus :=
    Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryPlusFactorsh.symm
  exact Functor.rightDerivedNatIso _ _
    (F ⋙ G).rightDerivedFunctorPlusUnith
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso C) e

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
