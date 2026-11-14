import Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.Parabolic.RefinementComposition

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinementComposition`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinementComposition` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic
open Langlands.GeneralLinear
open Langlands.Geometric
universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.Parabolic
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric
open Langlands.Parabolic
open scoped NNReal
universe u
variable {F : LocalFieldPackage.{u}}
variable (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The outer modulus factors through the actual inner Levi projection. -/
theorem refinedOuterModulus_projection (q : refinedParabolic F.Carrier B S) :
    T.refinedOuterModulus B S (refinedLeviProjection F.Carrier B S q) =
      T.leviModulus B q.val := by
  have hu := T.leviModulus_refinedUnipotent B S
    ⟨(refinedUnipotentPart F.Carrier B S q).val.val,
      (mem_refinedUnipotentRadical F.Carrier B S _).mp
        (refinedUnipotentPart F.Carrier B S q).property⟩
  change T.leviModulus B
    (q.val * (refinedLeviProjection F.Carrier B S q).val⁻¹) = 1 at hu
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu.symm

theorem refinedOuterHalfModulus_projection (q : refinedParabolic F.Carrier B S) :
    T.refinedOuterHalfModulus B S (refinedLeviProjection F.Carrier B S q) =
      T.leviHalfModulus B q.val := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.leviModulus B))
    (refinedLeviProjection F.Carrier B S q).val = _
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom)
      (T.refinedOuterModulus B S (refinedLeviProjection F.Carrier B S q))) = _
  rw [T.refinedOuterModulus_projection B S]
  rfl

/-- Product of the outer rectangular-block contributions and the inner contributions. -/
def composedLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  T.refinedOuterModulus B S * T.refinedLeviModulus B S

/-- The canonical positive half, used for direct normalized induction. -/
def composedLeviHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.composedLeviModulus B S))

theorem composedLeviHalfModulus_eq :
    T.composedLeviHalfModulus B S =
      T.refinedOuterHalfModulus B S * T.refinedLeviHalfModulus B S := by
  ext m
  simp [composedLeviHalfModulus, composedLeviModulus, refinedOuterHalfModulus,
    refinedOuterModulus, refinedLeviHalfModulus, leviHalfModulus,
    Jacquet.complexCharacter, Jacquet.positiveHalfCharacter]

/-- The positive induction character on the actual composite parabolic. -/
def composedParabolicHalfModulus : composedParabolic F.Carrier B S →* ℂˣ :=
  (T.composedLeviHalfModulus B S).comp (composedLeviProjection F.Carrier B S)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
