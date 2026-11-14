import Langlands.GroupScheme.IntegralModelReduction

/-! # Generic images of special-fibre subgroup preimages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- The generic points of integral sections whose reductions lie in `P`. -/
def specialFibreSubgroupPoints (P : Subgroup (rationalPoints M.specialFibre)) :
    Subgroup (rationalPoints G) :=
  (P.comap M.reduction).map M.integralPointMap

theorem mem_specialFibreSubgroupPoints
    (P : Subgroup (rationalPoints M.specialFibre)) (g : rationalPoints G) :
    g ∈ M.specialFibreSubgroupPoints P ↔
      ∃ x : M.integralSections,
        M.reduction x ∈ P ∧ M.integralPointMap x = g :=
  Iff.rfl

theorem specialFibreSubgroupPoints_le_integralPoints
    (P : Subgroup (rationalPoints M.specialFibre)) :
    M.specialFibreSubgroupPoints P ≤ M.integralPoints := by
  rintro g ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

end Langlands.GroupScheme.IntegralModel
