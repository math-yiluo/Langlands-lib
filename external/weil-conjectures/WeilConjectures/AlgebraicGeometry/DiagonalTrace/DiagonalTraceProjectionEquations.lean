/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-! # Shared categorical parameters for finite projection equations -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- A finite projection equation with its category structures shared explicitly.
Source: diagonal trace proof (1), normalized root projection.
(blueprint: def-sfb-diagonal-trace-root-projection-equation). -/
@[irreducible]
def rootProjectionEquation
    {C D : Type*} [Category C] [Category D]
    (R E : C ⥤ D) (pi : R ⟶ E) {I J : C} {M : D}
    (a : M ⟶ R.obj I) (b : I ⟶ J) (d : M ⟶ E.obj J) : Prop :=
  a ≫ pi.app I ≫ E.map b = d

/-- The finite boundary equation with each categorical interface shared by name.
Source: diagonal trace proof (2), projecting the supported Cartier class.
(blueprint: def-sfb-diagonal-trace-supported-boundary-equation). -/
@[irreducible]
def supportedBoundaryEquation
    {A C D : Type*} [Category A] [Category C] [Category D]
    (U : A ⥤ D) (R E : C ⥤ D) (pi : R ⟶ E)
    {P Q : A} {K J W : C}
    (g : P ⟶ Q) (s : U.obj Q ⟶ R.obj K) (f : K ⟶ J)
    (b : J ⟶ W) (v : U.obj P ⟶ E.obj W) : Prop :=
  U.map g ≫ s ≫ pi.app K ≫ E.map f ≫ E.map b = v

/-- The completed supported input followed by its target comparison equals the
specified finite Chern arrow. This is an actual composite equation.
Source: diagonal trace proof, precomposing the whole-system equation.
(blueprint: def-sfb-diagonal-trace-completed-boundary-equation). -/
@[irreducible]
def completedBoundaryEquation
    {C D : Type*} [Category C] [Category D]
    (U : C ⥤ D) {W X Y : C} {Z : D}
    (g : W ⟶ X) (delta : X ⟶ Y) (z : U.obj Y ⟶ Z) (v : U.obj W ⟶ Z) : Prop :=
  U.map (g ≫ delta) ≫ z = v

end AlgebraicGeometry.ProEtale.DiagonalTrace
