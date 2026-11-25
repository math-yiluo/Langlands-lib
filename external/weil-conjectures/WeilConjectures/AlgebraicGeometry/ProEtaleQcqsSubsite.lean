/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# The qcqs subcategory of the small pro-etale site

Source: Stacks Project, Tag 09A1, proof of lemma-w-contractible-hypercovering,
qcqs subsite paragraph (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- The qcqs objects of the small pro-etale site, Stacks Project, Tag 09A1.
(auxiliary; not a blueprint node) -/
def qcqsObjects (X : Scheme.{u}) : ObjectProperty X.ProEt :=
  fun U ↦ CompactSpace U.left ∧ QuasiSeparatedSpace U.left

/-- The full subcategory of qcqs objects, Stacks Project, Tag 09A1.
(auxiliary; not a blueprint node) -/
abbrev Qcqs (X : Scheme.{u}) := (qcqsObjects X).FullSubcategory

/-- The inclusion of the qcqs subcategory, Stacks Project, Tag 09A1.
(auxiliary; not a blueprint node) -/
def qcqsInclusion (X : Scheme.{u}) : Qcqs X ⥤ X.ProEt := (qcqsObjects X).ι

/-- Finite pro-etale covering families on the qcqs subcategory, Stacks Project,
Tag 09A1. A finite presieve represents a finite family, with repetitions forgotten.
(auxiliary; not a blueprint node) -/
def qcqsPrecoverage (X : Scheme.{u}) : Precoverage (Qcqs X) :=
  (precoverage X).comap (qcqsInclusion X) ⊓ Precoverage.finite (Qcqs X)

end AlgebraicGeometry.Scheme.ProEt
