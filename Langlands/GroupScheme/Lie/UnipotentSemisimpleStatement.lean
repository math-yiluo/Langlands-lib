import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Semisimple tangent elements of unipotent algebraic groups -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An affine unipotent algebraic group has no nonzero actual tangent element
whose differential is geometrically semisimple in every algebraic representation. -/
def UnipotentSemisimpleStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom → IsUnipotent G →
      ∀ X : lieKernel G k, Lie.IsSemisimpleElement G X → X = 1

end Langlands.GroupScheme
