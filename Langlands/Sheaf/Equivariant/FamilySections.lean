import Langlands.Sheaf.Equivariant.ActionOpens
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Indexed coefficient families on transport opens -/

namespace Langlands.Cohomology.CompactSoft

open Langlands.Sheaf.Equivariant

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X]

/-- The coordinate type for a coinduced sheaf of arbitrary coefficient families. -/
abbrev FamilySections (A : X → ModuleCat.{u} R) (U : ActionOpens G X) :=
  ∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), A y.1

end Langlands.Cohomology.CompactSoft
