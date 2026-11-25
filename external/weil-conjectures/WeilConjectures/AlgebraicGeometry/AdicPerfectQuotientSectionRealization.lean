/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleFunctors
public import WeilConjectures.AlgebraicGeometry.AdicPerfectSliceSections
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction

/-! # Explicit section adjoints for the ordinary quotient realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.AdicQuotientSections

attribute [local irreducible] derivedExtension extend change
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

section Quotient
variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ)

/-- The quotient map after restriction to the slice. Source: Stacks 09C6
(auxiliary; not a blueprint node). -/
def quotientMap :
    (constant (coefficientProEtaleModelTopology.{u, v} X) A).over U ⟶
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U :=
  ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (ConstantCompletion.quotient (coefficientProEtaleModelTopology.{u, v} X) A J n)

/-- Direct ordinary realization over the constant quotient ring on the slice.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
def quotientRealization : ModuleCat.{max v (u + 1)} A ⥤
    Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  localConstant (coefficientProEtaleModelTopology.{u, v} X) A U ⋙
    change (quotientMap X J U n)

/-- Algebraic terminal sections of a quotient-ring module sheaf.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def rawRightAdjoint :
    Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
      ModuleCat.{max v (u + 1)} A :=
  res (quotientMap X J U n) ⋙
    localSections (coefficientProEtaleModelTopology.{u, v} X) A U

/-- The direct quotient realization/sections rawAdjunction.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
theorem quotientAdjunction_exists :
    Nonempty (quotientRealization X J U n ⊣ rawRightAdjoint X J U n) :=
  ⟨(localAdjunction (coefficientProEtaleModelTopology.{u, v} X) A U).comp
    (AdicPerfectModel.scalarAdjunction (quotientMap X J U n))⟩

/-- Compose the constant-module and tensor adjunctions. Source: Stacks 03CY, 03EK
(auxiliary; not a blueprint node). -/
def quotientAdjunction : quotientRealization X J U n ⊣ rawRightAdjoint X J U n :=
  Classical.choice (quotientAdjunction_exists X J U n)

/-- Cancel completion in the ordinary realization, by the completion cone equation.
Source: Stacks 03EK, 09C6 (auxiliary; not a blueprint node). -/
theorem realizationIso_exists : Nonempty (adicPerfectQuotientFunctor X J U n ≅
    quotientRealization X J U n) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let φ := coefficientMap T A J
  let π := projection T A J n
  let q := ConstantCompletion.quotient T A J n
  let K := commutativeSiteConstantModuleFunctor T A
  have h : φ ≫ π = q := by
    exact limit.lift_π (quotientCone T A J) (op n)
  let pres := AdicPerfectModel.constantPresentationIso (J := T) (A := A)
  exact ⟨Functor.isoWhiskerRight pres
      (change φ ⋙ SheafOfModules.overFunctor _ U ⋙
        change (adicResidueLocalProjection X J U n)) ≪≫
    Functor.isoWhiskerLeft (K ⋙ change φ) (changeOverIso T U π) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft K
        (adicFiniteChangeComp φ π ≪≫ eqToIso (congrArg change h)))
      (SheafOfModules.overFunctor _ U) ≪≫
    (Functor.isoWhiskerLeft K (changeOverIso T U q)).symm ≪≫
    Functor.isoWhiskerRight (localConstantIso T A U).symm (change (quotientMap X J U n))⟩

/-- The explicit direct-quotient normalization. Source: Stacks 03EK, 09C6
(auxiliary; not a blueprint node). -/
def realizationIso : adicPerfectQuotientFunctor X J U n ≅
    quotientRealization X J U n :=
  Classical.choice (realizationIso_exists X J U n)

/-- Transport the constructed rawAdjunction to the actual completed quotient functor.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
theorem rawAdjunction_exists :
    Nonempty (adicPerfectQuotientFunctor X J U n ⊣ rawRightAdjoint X J U n) :=
  ⟨(quotientAdjunction X J U n).ofNatIsoLeft (realizationIso X J U n).symm⟩

/-- A sections rawAdjunction for the actual completed quotient functor.
The preceding theorem constructs one without any unproved existence result.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
def rawAdjunction : adicPerfectQuotientFunctor X J U n ⊣ rawRightAdjoint X J U n :=
  Classical.choice (rawAdjunction_exists X J U n)

end Quotient
end AlgebraicGeometry.Scheme.AdicQuotientSections
