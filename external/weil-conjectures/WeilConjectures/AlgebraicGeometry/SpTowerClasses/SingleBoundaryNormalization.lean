/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite

/-! # Finite boundary comparison with shared single-complex witnesses

Source: blueprint classes clause (3), finite supported normalization.
(blueprint: def-sp-single-boundary-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Form the finite boundary predicate before specializing the abelian category.
The quotient is placed in degree zero and the root map in degree zero shifted by two.
The two supplied arrows retain exactly the endpoint transports of `finiteBoundaryEquality`.
Source: classes (2)--(3), finite Kummer boundary and supported Cartier boundary.
(blueprint: def-sp-single-boundary-normalization).

Construction: apply the degree-zero single functor to the quotient and the root map,
shift the latter by two, and use these actual morphisms in `finiteBoundaryEquality`.
No choice of arrow or endpoint transport is added; unfolding gives the original predicate,
including its heterogeneous equalities and final ordinary equality. -/
def singleBoundaryEquality {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {X X' Y Y' : C} (q : X ⟶ X') (r : Y ⟶ Y')
    {A B : Type w} (a : A) (beta : B) : Prop :=
  finiteBoundaryEquality ((DerivedCategory.singleFunctor C 0).map q)
    (((DerivedCategory.singleFunctor C 0).map r)⟦(2 : ℤ)⟧') a beta

end AlgebraicGeometry.ProEtale.SpTowerClasses
