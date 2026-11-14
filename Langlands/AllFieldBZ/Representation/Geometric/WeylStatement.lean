import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.Geometric.WeylStatement

/-!
# All-field port of `Langlands.Representation.Geometric.WeylStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.WeylStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.GeneralLinear
universe uF

/-- The actual inverse permutation matrices parametrize parabolic double
cosets for every finite extension of a p-adic field. -/
def PadicParabolicBruhatTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n),
      Function.Bijective (parabolicDoubleCoset F.Carrier B C)

/-- The two actual intersection triples are standard parabolic triples in
their product Levis. Their refinements consist of actual positive blocks. -/
def PadicStandardIntersectionsTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
      (w : MinimalRepresentatives B C),
      (∃ S : BlockRefinement B,
        sourceParabolic F.Carrier B C w.val = refinedParabolic F.Carrier B S ∧
        sourceLevi F.Carrier B C w.val = refinedLevi F.Carrier B S ∧
        sourceUnipotent F.Carrier B C w.val = refinedUnipotent F.Carrier B S) ∧
      (∃ T : BlockRefinement C,
        sourceParabolic F.Carrier C B w.val⁻¹ = refinedParabolic F.Carrier C T ∧
        sourceLevi F.Carrier C B w.val⁻¹ = refinedLevi F.Carrier C T ∧
        sourceUnipotent F.Carrier C B w.val⁻¹ = refinedUnipotent F.Carrier C T)

end Langlands.AllFieldBZ.Geometric
