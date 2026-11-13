import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.AllField.Representation.Geometric.RefinementDefinitions
import Langlands.AllField.Representation.Parabolic.RefinementCharacter
/-! The actual composite parabolic for a refinement of an ordered block shape. -/

noncomputable section

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic
open Langlands.AllField.Parabolic

open Langlands.GeneralLinear
open Langlands.Geometric

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllField.Parabolic

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric
open Langlands.Parabolic
open Langlands.AllField.Parabolic
open scoped NNReal

universe u
variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Product of the outer rectangular-block contributions and the inner contributions. -/
def composedLeviModulus : refinedLevi F B S →* ℝ≥0ˣ :=
  T.refinedOuterModulus B S * T.refinedLeviModulus B S

/-- The canonical positive half, used for direct normalized induction. -/
def composedLeviHalfModulus : refinedLevi F B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.composedLeviModulus B S))

theorem composedLeviHalfModulus_eq :
    T.composedLeviHalfModulus B S =
      T.refinedOuterHalfModulus B S * T.refinedLeviHalfModulus B S := by
  ext m
  simp [composedLeviHalfModulus, composedLeviModulus, refinedOuterHalfModulus,
    refinedOuterModulus, refinedLeviHalfModulus, leviHalfModulus,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter]

end Langlands.LocalFieldData
