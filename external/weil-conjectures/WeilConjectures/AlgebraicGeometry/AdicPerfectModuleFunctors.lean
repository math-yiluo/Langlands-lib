/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes

/-! # Ordinary completed quotient realization of modules

Source: Stacks Project, Tags 093T and 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change

/-- The actual completed constant module on the slice, before reduction.
Source: Stacks Tag 09C6 (auxiliary; not a blueprint node). -/
def adicPerfectLocalFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  SheafOfModules.strictPerfectConstantSheaf
      (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
    SheafOfModules.overFunctor _ U

instance adicPerfectModuleFunctorsInst1 (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    (adicPerfectLocalFunctor X J U).Additive := by
  exact inferInstanceAs
    ((SheafOfModules.strictPerfectConstantSheaf
        (coefficientProEtaleModelTopology.{u, v} X) A ⋙
      SheafOfModules.restrictScalars
        (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
      change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
      SheafOfModules.overFunctor _ U).Additive)

/-- The ordinary quotient realization on modules, with its actual scalar ring.
Source: Stacks Tag 09C6 (auxiliary; not a blueprint node). -/
def adicPerfectQuotientFunctor (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    ModuleCat.{max v (u + 1)} A ⥤
      Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  adicPerfectLocalFunctor X J U ⋙ change (adicResidueLocalProjection X J U n)

instance adicPerfectModuleFunctorsInst2 (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    (adicPerfectQuotientFunctor X J U n).Additive := by
  have := change_additive (adicResidueLocalProjection X J U n)
  unfold adicPerfectQuotientFunctor
  infer_instance

/-- The ordinary module balancing isomorphism at a successor level.
Source: Stacks Tags 06YY and 09C6 (auxiliary; not a blueprint node). -/
def adicPerfectQuotientModuleStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicPerfectQuotientFunctor X J U (n + 1) ⋙
        change (adicPerfectQuotientScalarStep X J U n) ≅
      adicPerfectQuotientFunctor X J U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (adicPerfectLocalFunctor X J U)
      (adicFiniteChangeComp (adicResidueLocalProjection X J U (n + 1))
        (adicPerfectQuotientScalarStep X J U n) ≪≫
          eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp X J U n)))

end AlgebraicGeometry.Scheme
