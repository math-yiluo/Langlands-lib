import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement
import Langlands.AllField.Representation.Parabolic.RefinementComposition
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

/-- The outer modulus factors through the actual inner Levi projection. -/
theorem refinedOuterModulus_projection (q : refinedParabolic F B S) :
    T.refinedOuterModulus B S (refinedLeviProjection F B S q) =
      T.leviModulus B q.val := by
  have hu := T.leviModulus_refinedUnipotent B S
    ⟨(refinedUnipotentPart F B S q).val.val,
      (mem_refinedUnipotentRadical F B S _).mp
        (refinedUnipotentPart F B S q).property⟩
  change T.leviModulus B
    (q.val * (refinedLeviProjection F B S q).val⁻¹) = 1 at hu
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu.symm

theorem refinedOuterHalfModulus_projection (q : refinedParabolic F B S) :
    T.refinedOuterHalfModulus B S (refinedLeviProjection F B S q) =
      T.leviHalfModulus B q.val := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))
    (refinedLeviProjection F B S q).val = _
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.refinedOuterModulus B S (refinedLeviProjection F B S q))) = _
  rw [T.refinedOuterModulus_projection B S]
  rfl

/-- The positive induction character on the actual composite parabolic. -/
def composedParabolicHalfModulus : composedParabolic F B S →* ℂˣ :=
  (T.composedLeviHalfModulus B S).comp (composedLeviProjection F B S)

end Langlands.LocalFieldData
