/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.UniformFiniteFilteredLocalization
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import WeilConjectures.CategoryTheory.FiniteFilteredGradedExactness
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Quotient

/-!
# Actual filtered homotopy classes and their graded quasi-isomorphisms

Source: Stacks Project, Derived Categories, Section 13.13, Tags 05S1--05S6.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A chain homotopy preserving every filtration step, including all its components.
Source: Stacks, Section 13.13, before Tag 05S1
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
def UniformFilteredHomotopy {K L : WeilFilteredObject (CochainComplex C ℤ)}
    (f g : K ⟶ L) : Prop :=
  ∃ h : Homotopy f.hom g.hom, ∀ p n m : ℤ,
    ∃ lift : (K.filtration.F p : CochainComplex C ℤ).X n ⟶
      (L.filtration.F p : CochainComplex C ℤ).X m,
      lift ≫ (L.filtration.F p).arrow.f m =
        (K.filtration.F p).arrow.f n ≫ h.hom n m

-- The following two universal-property arguments follow the private helpers in
-- Sheaf.CategoryTheory.FilteredHomotopySpectralSequence (group E1).
/-- Filtered homotopy as a relation on the chosen full subcategory.
Source: Stacks, Section 13.13, before Tag 05S1
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
def uniformFilteredHomotopyRel (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) : HomRel (UniformFilteredComplexes C B P) :=
  fun _ _ f g ↦ UniformFilteredHomotopy f.hom g.hom

/-- The zero homotopy preserves every filtration step.
Source: Stacks, Section 13.13. The indicated component operations preserve each step.
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
theorem UniformFilteredHomotopy.refl {K L : WeilFilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) :
    UniformFilteredHomotopy f f := by
  refine ⟨Homotopy.refl f.hom, fun p n m ↦ ⟨0, ?_⟩⟩
  simp

/-- Negating the component lifts reverses a filtered homotopy.
Source: Stacks, Section 13.13. The indicated component operations preserve each step.
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
theorem UniformFilteredHomotopy.symm {K L : WeilFilteredObject (CochainComplex C ℤ)}
    {f g : K ⟶ L} (h : UniformFilteredHomotopy f g) : UniformFilteredHomotopy g f := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.symm, ?_⟩
  intro p n m
  obtain ⟨l, hl⟩ := hH p n m
  exact ⟨-l, by simpa using congrArg Neg.neg hl⟩

/-- The actual quotient by filtration-preserving chain homotopies.
Source: Stacks, Tag 05S1
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
abbrev UniformFilteredHomotopyCategory (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ)) :=
  CategoryTheory.Quotient (uniformFilteredHomotopyRel (C := C) B P)

/-- The quotient functor to filtered homotopy classes.
Source: Stacks, Tag 05S1
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
abbrev uniformFilteredHomotopyQ (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    UniformFilteredComplexes C B P ⥤ UniformFilteredHomotopyCategory C B P :=
  CategoryTheory.Quotient.functor (uniformFilteredHomotopyRel B P)

/-- Graded quasi-isomorphisms in the quotient, expressed by a chain-map representative.
Source: Stacks, Tag 05S2
(blueprint: def-trf-uniform-filtered-homotopy-category). -/
def uniformFilteredHomotopyQuasiIso (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    MorphismProperty (UniformFilteredHomotopyCategory C B P) := fun {K L} f ↦
  ∃ g : K.as ⟶ L.as, (uniformFilteredHomotopyQ B P).map g = f ∧
    uniformFilteredQuasiIso B P g

end CategoryTheory

end
