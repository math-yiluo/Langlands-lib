/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Filtration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.BasicFilteredGlobalSurjection
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Basic filtered complexes surjecting on cohomology

Source: Stacks Project, More on Algebra, Tag 0H7X, lemma-resolution-filtered-complex,
construction of the initial basic filtered complex (blueprint:
lem-pur-kunneth-basic-filtered-surjection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- `B` is basic when all terms of `B`, of each filtered subcomplex, and of each graded
piece are free modules, and every differential is zero. Source: Stacks Project, More on
Algebra, Tag 0H7X, lemma-resolution-filtered-complex (blueprint:
lem-pur-kunneth-basic-filtered-surjection). -/
def BasicFilteredComplex (R : Type u) [CommRing R]
    (B : WeilFilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) :
    Prop :=
  (∀ n : ℤ, Module.Free R (B.obj.X n)) ∧
  (∀ (i n : ℤ), Module.Free R ((B.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
  (∀ (i n : ℤ), Module.Free R ((B.filtration.gr i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
  (∀ (n m : ℤ), B.obj.d n m = 0)

end CategoryTheory
