import Langlands.GroupScheme.Rational.RootCharacterKernel
import Langlands.Geometry.Building.RootDatumValuation
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Root points lie in every character-valuation kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)

include hS ha

/-- All rational characters are one on actual root points, so every valuation
of those characters is one as well. -/
theorem rootGroupPoints_le_characterValuationKernel :
    rootGroupPoints i a ≤ characterValuationKernel v G := by
  intro g hg
  apply mem_characterValuationKernel.mpr
  intro ψ
  have h := RelativeRoot.characterEval_eq_one_of_mem_subgroup hS i a ha ψ hg
  have heq : rationalCharacterEval ψ g = 1 := by
    change Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom
      (characterEval ψ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) g) = 1
    rw [h, map_one]
  rw [heq, Units.val_one, map_one]

/-- Intersecting actual root points with a one-fixer imposes only its fixer
condition, since the character-valuation condition is automatic. -/
theorem rootGroupPoints_inf_characterValuationKernel_inf
    (H : Subgroup (rationalPoints G)) :
    rootGroupPoints i a ⊓ (characterValuationKernel v G ⊓ H) =
      rootGroupPoints i a ⊓ H := by
  rw [← inf_assoc, inf_eq_left.mpr (rootGroupPoints_le_characterValuationKernel hS i a ha v)]

end Langlands.Geometry.Building
