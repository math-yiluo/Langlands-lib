import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryStatement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Geometry of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The geometric properties needed to equip the actual chosen dual group scheme
with an abelian-scheme structure. This predicate makes sense over every base. -/
def DualSchemeGeometry {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A) :
    Prop :=
  Smooth (dualScheme A hA).hom ∧ IsProper (dualScheme A hA).hom ∧
    GeometricallyConnected (dualScheme A hA).hom

/-- Over a quasi-separated base, the actual universal Picard-zero parameter scheme
has the geometric properties of an abelian scheme. -/
def RelativeDualSchemeGeometryStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), DualSchemeGeometry A hA

/-- The relative geometry target implies the existing field geometry target. -/
lemma RelativeDualSchemeGeometryStatement.field
    (geometry : RelativeDualSchemeGeometryStatement.{u}) :
    FieldDualSchemeGeometryStatement.{u} := by
  intro k _ A hA
  exact geometry _ A hA

end Langlands.AbelianScheme
