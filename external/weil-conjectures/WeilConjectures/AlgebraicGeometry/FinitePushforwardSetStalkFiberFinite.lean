/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- (blueprint: lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite)
The geometric fibre of a finite morphism over an algebraically closed field is finite.

Source: Stacks Project, Proposition 59.55.2, Tag 03QP (1), first display and its
proof. Base change to the strict henselization at the geometric point is finite and
affine, hence its coordinate algebra is finite over a strictly henselian local ring.
The finite algebra decomposes into finitely many henselian local factors. Each residue
field is a finite extension of the separably closed residue field, so each factor is
strictly henselian and has one geometric point over the fixed algebraically closed
field. The factors therefore biject with the geometric points in the fibre, giving
the required finite typeclass. -/
theorem finite_pushforward_set_stalk_fiber_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y} := by
  exact @Scheme.Hom.GeometricFiber.finite _ _ f Ω _ y _
end AlgebraicGeometry
