import Langlands.Algebra.CompatibleUnitization
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Zero-action separation of unitized finiteness conventions

Internal derived targets motivated by the nonunital conventions of Renard
2026. They distinguish two actual unitized actions on the complex line,
without identifying the source's finiteness or Noetherian conventions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationZeroActionFiniteness

universe uA

/-- The complex-unitized zero action on the complex line is finite and
Noetherian for every bilinear nonunital complex algebra. -/
def ComplexZeroActionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A],
    letI := CompatibleUnitization.module (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)
    Module.Finite (Unitization ℂ A) ℂ ∧ IsNoetherian (Unitization ℂ A) ℂ

/-- The integer-unitized zero action on the same complex line is neither
finite nor Noetherian for any nonunital ring. -/
def IntegerZeroActionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := CompatibleUnitization.module (0 : A →ₙₐ[ℤ] Module.End ℤ ℂ)
    ¬ Module.Finite (Unitization ℤ A) ℂ ∧ ¬ IsNoetherian (Unitization ℤ A) ℂ

/-- The positive complex and negative integer zero-action targets, in order. -/
def ZeroActionFinitenessStatements : Prop :=
  ComplexZeroActionStatement.{uA} ∧ IntegerZeroActionStatement.{uA}

end Langlands.Algebra.UnitizationZeroActionFiniteness
