import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.AllField.Group.GL.BlockModulus
/-! Intrinsic projection and explicit modulus for a parabolic in a product Levi. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.Geometric
open Langlands.AllField.Geometric
open scoped BigOperators NNReal

universe u
variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : BlockRefinement B)

/-- The inner block coordinates of one actual refined Levi element. -/
def refinedLeviBlock (i : Fin B.length) :
    refinedLevi F B S →* (S i).Levi F :=
  ((S i).leviEquiv F).symm.toMonoidHom.comp (refinedLeviEval F B S i)

/-- Product of the published explicit positive moduli of the inner parabolics. -/
def refinedLeviModulus : refinedLevi F B S →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, (T.leviModulus (S i)).comp (refinedLeviBlock B S i)

theorem refinedLeviModulus_apply (m : refinedLevi F B S) :
    T.refinedLeviModulus B S m =
      ∏ i : Fin B.length, T.leviModulus (S i) (refinedLeviBlock B S i m) := by
  simp [refinedLeviModulus]

/-- Positive complex half of the full product modulus, for induction. -/
def refinedLeviHalfModulus : refinedLevi F B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.refinedLeviModulus B S))

/-- Canonical inverse half of the same full modulus, for Jacquet normalization. -/
def refinedLeviInverseHalfModulus : refinedLevi F B S →* ℂˣ :=
  Jacquet.inverseHalfCharacter (T.refinedLeviModulus B S)

@[simp] theorem refinedLeviHalfModulus_apply (m : refinedLevi F B S) :
    (T.refinedLeviHalfModulus B S m : ℂ) =
      ((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ) := rfl

@[simp] theorem refinedLeviInverseHalfModulus_apply (m : refinedLevi F B S) :
    (T.refinedLeviInverseHalfModulus B S m : ℂ) =
      (((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ))⁻¹ :=
  Jacquet.inverseHalfCharacter_apply _ _

end Langlands.LocalFieldData
