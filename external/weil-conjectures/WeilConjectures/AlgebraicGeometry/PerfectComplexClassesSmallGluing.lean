/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallGluingCore

/-! # Gluing smallness of perfect isomorphism classes

Source: Step 2 of lem-pc-perfect-complexes-compact-set, using Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

theorem perfectComplex_classesSmallOnOpen_union (X : Scheme.{u})
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V)
    (pU : PerfectComplexClassesSmallOnOpen.{u, w} X U)
    (pV : PerfectComplexClassesSmallOnOpen.{u, w} X V)
    (pUV : PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊓ V)) :
    PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊔ V) := by
  intro Y f inst hr _ _
  exact perfectComplex_classesSmallOnOpen_union_core X U V hU hV pU pV pUV Y f hr

end AlgebraicGeometry.Scheme
