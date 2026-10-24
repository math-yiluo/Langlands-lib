import Langlands.AlgebraicGeometry.Picard.LocalComparisonStatement

/-!
# The two directions of the scheme local rank-one comparison

These proposition definitions separate the existing comparison into independently
provable implications. This file supplies no proof of either implication.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A locally free rank-one module sheaf has an inverse for the actual scheme
sheaf tensor. This definition states the implication. -/
def LocallyFreeRankOneTensorInvertibleStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    IsLocallyFreeRankOne M → Langlands.CategoryTheory.TensorInvertible M

/-- A module sheaf invertible for the actual scheme sheaf tensor admits rank-one
trivializations on neighborhoods. This definition states the implication. -/
def TensorInvertibleLocallyFreeRankOneStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    Langlands.CategoryTheory.TensorInvertible M → IsLocallyFreeRankOne M

/-- The paired directional statements, selected together for statement review. -/
def LocalComparisonDirectionsStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  LocallyFreeRankOneTensorInvertibleStatement X ∧
    TensorInvertibleLocallyFreeRankOneStatement X

end Langlands.AlgebraicGeometry.Picard
