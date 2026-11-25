/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Uniformly finite filtered cochain localizations

Source: Stacks Project, Derived Categories, Tags 05S2, 05S4, 05S5 and 05S6,
restricted to uniformly finite filtrations, as in the trace-formula comparison
(blueprint: def-trf-uniform-finite-filtered-localization).

Filtrations are subobjects in the abelian category of cochain complexes. Thus their
finite bounds are uniform in cochain degree. `B = some (a,b)` fixes those bounds;
`B = none` allows them to depend on the complex. `P` specifies cochain boundedness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Uniform finite filtration bounds, optional fixed interval, and cochain condition `P`.
Source: Stacks, Tags 05S2 and 05S4, restricted uniformly in cochain degree
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredProperty (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    ObjectProperty (WeilFilteredObject (CochainComplex C ℤ)) := fun K ↦
  K.filtration.IsFinite ∧
    (∀ a b : ℤ, B = some (a, b) →
      K.filtration.F a = ⊤ ∧ K.filtration.F (b + 1) = ⊥) ∧ P K.obj

/-- Cochain-bounded uniformly finite filtered complexes and filtered chain maps.
Source: Stacks, Tags 05S2 and 05S4
(blueprint: def-trf-uniform-finite-filtered-localization). -/
abbrev UniformFilteredComplexes (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ)) :=
  (uniformFilteredProperty B P).FullSubcategory

/-- The graded quasi-isomorphisms, using the existing canonical graded chain map.
Source: Stacks, Tag 05S2
(blueprint: def-trf-uniform-finite-filtered-localization). -/
def uniformFilteredQuasiIso (B : Option (ℤ × ℤ))
    (P : ObjectProperty (CochainComplex C ℤ)) :
    MorphismProperty (UniformFilteredComplexes C B P) := fun _ _ f ↦
  ∀ p : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps f.hom p)

end CategoryTheory
