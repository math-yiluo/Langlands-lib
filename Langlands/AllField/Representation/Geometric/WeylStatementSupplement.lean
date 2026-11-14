import Langlands.Representation.Geometric.WeylStatement
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.Representation.Geometric.WeylStatement
/-! Concrete GL specializations of the Weyl and Bruhat prerequisites of BZ77. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe uF

/-- The two actual intersection triples are standard parabolic triples in
their product Levis. Their refinements consist of actual positive blocks. -/
def PadicStandardIntersectionsTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
      (w : MinimalRepresentatives B C),
      (∃ S : BlockRefinement B,
        sourceParabolic F B C w.val = refinedParabolic F B S ∧
        sourceLevi F B C w.val = refinedLevi F B S ∧
        sourceUnipotent F B C w.val = refinedUnipotent F B S) ∧
      (∃ T : BlockRefinement C,
        sourceParabolic F C B w.val⁻¹ = refinedParabolic F C T ∧
        sourceLevi F C B w.val⁻¹ = refinedLevi F C T ∧
        sourceUnipotent F C B w.val⁻¹ = refinedUnipotent F C T)

end Langlands.AllField.Geometric
