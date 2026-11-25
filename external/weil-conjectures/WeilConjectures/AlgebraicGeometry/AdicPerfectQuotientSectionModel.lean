/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionRealization

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

section Package
variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
  (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)

attribute [local irreducible] adicPerfectQuotientFunctor adicPerfectQuotientModuleStep

/-- The ordinary adjunction tower, with its proved unit identity stored as a field.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
structure SectionModel where
  R : ∀ n : ℕ,
    Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
      ModuleCat.{max v (u + 1)} A
  a : ∀ n : ℕ, adicPerfectQuotientFunctor X J U n ⊣ R n
  κ : ∀ n : ℕ, R (n + 1) ⟶
    change (adicPerfectQuotientScalarStep X J U n) ⋙ R n
  unit_eq : ∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
    (a n).unit.app M = (a (n + 1)).unit.app M ≫
      (κ n).app ((adicPerfectQuotientFunctor X J U (n + 1)).obj M) ≫
        (R n).map ((adicPerfectQuotientModuleStep X J U n).hom.app M)

/-- Assemble a tower from arbitrary adjunctions by the general mate construction.
The functors and adjunctions remain parameters throughout this proof.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
def SectionModel.ofAdjunctions
    (R : ∀ n : ℕ,
      Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
        ModuleCat.{max v (u + 1)} A)
    (a : ∀ n : ℕ, adicPerfectQuotientFunctor X J U n ⊣ R n) :
    SectionModel X J U where
  R := R
  a := a
  κ n := balancingMate
    (F₀ := adicPerfectQuotientFunctor X J U n) (R₀ := R n)
    (F₁ := adicPerfectQuotientFunctor X J U (n + 1)) (R₁ := R (n + 1))
    (C₀ := change (adicPerfectQuotientScalarStep X J U n))
    (a n) (a (n + 1)) (adicPerfectQuotientModuleStep X J U n)
  unit_eq n M := balancingMate_unit
    (F₀ := adicPerfectQuotientFunctor X J U n) (R₀ := R n)
    (F₁ := adicPerfectQuotientFunctor X J U (n + 1)) (R₁ := R (n + 1))
    (C₀ := change (adicPerfectQuotientScalarStep X J U n))
    (a n) (a (n + 1)) (adicPerfectQuotientModuleStep X J U n) M

/-- Supply the concrete terminal sections adjoints to the general constructor.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
theorem sectionModel_exists : Nonempty (SectionModel X J U) :=
  ⟨SectionModel.ofAdjunctions X J U (rawRightAdjoint X J U) (rawAdjunction X J U)⟩

/-- An adjunction tower selected from the preceding completely proved construction.
Its fields are abstract interfaces, so consumers do not reduce scalar tensor implementations.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
def sectionModel : SectionModel X J U := Classical.choice (sectionModel_exists X J U)

/-- The right adjoints of the constructed tower.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def rightAdjoint : ∀ n : ℕ,
    Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
      ModuleCat.{max v (u + 1)} A :=
  (sectionModel X J U).R

attribute [local irreducible] rightAdjoint

/-- The adjunctions of the constructed tower.
Source: Stacks 03CY, 03EK (auxiliary; not a blueprint node). -/
def adjunction : ∀ n : ℕ, adicPerfectQuotientFunctor X J U n ⊣
    rightAdjoint X J U n := by
  unfold rightAdjoint
  exact (sectionModel X J U).a

attribute [local irreducible] adjunction

/-- The scalar successor maps of the constructed tower.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def step : ∀ n : ℕ, rightAdjoint X J U (n + 1) ⟶
    change (adicPerfectQuotientScalarStep X J U n) ⋙ rightAdjoint X J U n := by
  unfold rightAdjoint
  exact (sectionModel X J U).κ

attribute [local irreducible] step

/-- The already proved unit equation of the constructed tower.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem step_unit (n : ℕ) (M : ModuleCat.{max v (u + 1)} A) :
    (adjunction X J U n).unit.app M =
      (adjunction X J U (n + 1)).unit.app M ≫
        (step X J U n).app ((adicPerfectQuotientFunctor X J U (n + 1)).obj M) ≫
          (rightAdjoint X J U n).map
            ((adicPerfectQuotientModuleStep X J U n).hom.app M) := by
  unfold adjunction step rightAdjoint
  exact (sectionModel X J U).unit_eq n M

end Package
end AlgebraicGeometry.Scheme.AdicQuotientSections
