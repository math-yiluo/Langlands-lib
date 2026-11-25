/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Boundary projections with integer indexing

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-boundary-projection).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- The image factor of the differential, indexed by its target degree.
Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-boundary-projection). -/
noncomputable def cartanEilenbergBoundaryProjection
    {B : Type u} [Category.{v} B] [Abelian B] (K : CochainComplex B ℤ) (p : ℤ) :
    K.X p ⟶ image (K.d ((p + 1) - 1) (p + 1)) :=
  eqToHom (congrArg K.X (by omega : p = (p + 1) - 1)) ≫
    factorThruImage (K.d ((p + 1) - 1) (p + 1))

/-- The boundary projection factors the differential.
Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-boundary-projection). -/
@[reassoc (attr := simp)]
theorem cartanEilenbergBoundaryProjection_fac
    {B : Type u} [Category.{v} B] [Abelian B] (K : CochainComplex B ℤ) (p : ℤ) :
    cartanEilenbergBoundaryProjection K p ≫ image.ι (K.d ((p + 1) - 1) (p + 1)) =
      K.d p (p + 1) := by
  simp [cartanEilenbergBoundaryProjection]

/-- The boundary inclusion factors through cycles.
Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-boundary-projection). -/
noncomputable def cartanEilenbergBoundaryInclusion
    {B : Type u} [Category.{v} B] [Abelian B] (K : CochainComplex B ℤ) (p : ℤ) :
    image (K.d (p - 1) p) ⟶ K.cycles p :=
  K.liftCycles (image.ι (K.d (p - 1) p)) (p + 1) (by simp) (by
    apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
    simp)

/-- The boundary-to-cycle map gives the image inclusion after including cycles.
Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-boundary-projection). -/
@[reassoc (attr := simp)]
theorem cartanEilenbergBoundaryInclusion_fac
    {B : Type u} [Category.{v} B] [Abelian B] (K : CochainComplex B ℤ) (p : ℤ) :
    cartanEilenbergBoundaryInclusion K p ≫ K.iCycles p = image.ι (K.d (p - 1) p) := by
  simp [cartanEilenbergBoundaryInclusion]

end CategoryTheory
