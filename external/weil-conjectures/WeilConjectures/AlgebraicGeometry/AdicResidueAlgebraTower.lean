/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.RingTheory.RlimPerfectComplete
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Algebraic stalk towers for finite adic reductions

Source: Stacks Project, proetale.tex, Tag 09C6, the normalized stalk system before
application of More on Algebra, Tag 09AW.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A normalized algebraic quotient tower, with its actual scalar-extension adjunctions.
The coefficient ring and its quotients need not be finite as sets.
Source: Stacks Project, Tags 09C6 and 09AW.
(auxiliary; not a blueprint node). -/
structure AdicResidueAlgebraTower {A : Type w} [CommRing A] (J : Ideal A) where
  level : ∀ n : ℕ, DerivedCategory (ModuleCat.{w} (A ⧸ J ^ (n + 1)))
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (DerivedCategory.adicStepRestriction J n).obj (level n)
  extension : ∀ n : ℕ, DerivedCategory (ModuleCat.{w} A) ⥤
    DerivedCategory (ModuleCat.{w} (A ⧸ J ^ (n + 1)))
  adjunction : ∀ n : ℕ, extension n ⊣ DerivedCategory.adicLevelRestriction J n
  stepExtension : ∀ n : ℕ,
    DerivedCategory (ModuleCat.{w} (A ⧸ J ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{w} (A ⧸ J ^ (n + 1)))
  stepAdjunction : ∀ n : ℕ, stepExtension n ⊣ DerivedCategory.adicStepRestriction J n
  normalized : ∀ n : ℕ, IsIso
    (((stepAdjunction n).homEquiv (level (n + 1)) (level n)).symm (transition n))
  residuePerfect : DerivedCategory.IsPerfect (level 0)

/-- Exact constant realization of an algebraic finite quotient on the actual slice.
The algebraic category uses the small Grothendieck localization; the sheaf category
uses the standard localization of the coefficient package.
Source: Stacks Project, Tags 093J, 03DJ and 09C6.
(auxiliary; not a blueprint node). -/
def adicResidueFiniteConstant (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :=
  letI := HasDerivedCategory.standard
    (CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.finite
        (coefficientProEtaleModelTopology.{u, v} X) A J n))
  commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
    max v (u + 1), max v (u + 1) + 1}
    (coefficientProEtaleModelTopology.{u, v} X) (A ⧸ J ^ (n + 1)) ⋙
      adicResidueRestriction.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite
          (coefficientProEtaleModelTopology.{u, v} X) A J n) U

end AlgebraicGeometry.Scheme
