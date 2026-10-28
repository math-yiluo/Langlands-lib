import Langlands.CategoryTheory.RenardFiniteType
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Renard's Noetherian comparisons for actual unital modules

Closed statement targets for Appendix A.I.3. The category comparison uses
a module-carrier universe containing a lift of the regular module.
-/

set_option autoImplicit false

namespace Langlands.Renard.ModuleNoetherian

universe uR uM

/-- Categorical Noetherianity agrees with algebraic Noetherianity for each
actual unital left module, with independent ring and carrier universes. -/
def ObjectStatement : Prop :=
  ∀ (R : Type uR) [Ring R] (M : ModuleCat.{uM} R),
    Langlands.Renard.IsNoetherianObject M ↔ IsNoetherian R M

/-- Renard's finite-type-based category convention agrees with left
Noetherianity of the ring, in a universe containing its regular module. -/
def CategoryStatement : Prop :=
  ∀ (R : Type uR) [Ring R],
    Langlands.Renard.IsNoetherianCategory (ModuleCat.{max uR uM} R) ↔
      IsNoetherianRing R

/-- The closed object and category comparisons, in that order. -/
def ModuleNoetherianStatement : Prop :=
  ObjectStatement.{uR, uM} ∧ CategoryStatement.{uR, uM}

end Langlands.Renard.ModuleNoetherian
