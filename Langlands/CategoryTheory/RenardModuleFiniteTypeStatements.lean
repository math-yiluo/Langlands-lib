import Langlands.CategoryTheory.RenardFiniteType
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Renard's finite-type example in the actual unital module category

Source: Renard (9 July 2026), Appendix A.I.3, printed pages 248–249.
These closed statements compare the published source-facing predicates with
ordinary finite generation. They assert no categorical characterization or
comparison for the larger category of possibly nonunital actions.
-/

set_option autoImplicit false

namespace Langlands.Renard.ModuleFiniteType

universe uR uM

/-- The A.I.3 example: categorical finite type for an actual unital left
module is equivalent to algebraic finite generation. -/
def FiniteTypeStatement : Prop :=
  ∀ (R : Type uR) [Ring R] (M : ModuleCat.{uM} R),
    IsFiniteTypeObject M ↔ Module.Finite R M

/-- The source finite-subcover property for an actual unital left module
is equivalent to algebraic finite generation. -/
def FiniteSubcoverStatement : Prop :=
  ∀ (R : Type uR) [Ring R] (M : ModuleCat.{uM} R),
    HasFiniteSubcoverProperty M ↔ Module.Finite R M

/-- The categorical finite-type and finite-subcover comparisons, in order. -/
def ModuleFiniteTypeStatement : Prop :=
  FiniteTypeStatement.{uR, uM} ∧ FiniteSubcoverStatement.{uR, uM}

end Langlands.Renard.ModuleFiniteType
