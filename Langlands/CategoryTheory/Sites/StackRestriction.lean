import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-! # Restricting stacks along an inclusion of Grothendieck topologies -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory

namespace Langlands.CategoryTheory.StackRestriction

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {J K : GrothendieckTopology C} (hJK : J ≤ K)

/-- Morphism descent for a larger topology implies it for a smaller topology. -/
abbrev prestack [F.IsPrestack K] : F.IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor
    (fun S R hR ↦ F.isPrestackFor' R (hJK S hR))

/-- Effective descent for a larger topology implies it for a smaller topology. -/
abbrev stack [F.IsStack K] : F.IsStack J :=
  Pseudofunctor.IsStack.of_isStackFor
    (fun S R hR ↦ F.isStackFor' R (hJK S hR))

end Langlands.CategoryTheory.StackRestriction
