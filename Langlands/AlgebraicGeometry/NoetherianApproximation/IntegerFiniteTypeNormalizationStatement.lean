import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalFiniteTypeSubalgebraStatement
import Mathlib.RingTheory.FiniteType

/-! # Finite normalization over the integers and its approximation reduction -/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- A finitely generated integer domain has finite normalization in its own fraction field. -/
def IntegerFiniteTypeNormalizationStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
    Module.Finite A (integralClosure A (FractionRing A))

/-- Finite normalization of integer domains suffices for normal subalgebra approximation. -/
def IntegerFiniteTypeNormalizationReductionStatement : Prop :=
  IntegerFiniteTypeNormalizationStatement.{u} → NormalFiniteTypeSubalgebraStatement.{u}

end Langlands.AlgebraicGeometry.NoetherianApproximation
