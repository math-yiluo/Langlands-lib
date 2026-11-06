import Langlands.Geometry.Building.SpecialPointFixedLocus

/-! # Special points as vertices of the actual valuation building -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace AffineRootSystem

/-- A special point of a rank-zero-compatible affine root system has singleton
facet, hence is a vertex. -/
theorem isVertex_of_isSpecialPoint
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {x : A} (hx : IsSpecialPoint Ψ x) : IsVertex Ψ x := by
  apply Set.Subset.antisymm
  · intro y hy
    exact Set.mem_singleton_iff.mpr
      (eq_of_isSpecialPoint_of_vanishingRoots hΨ hx
        (fun ψ hψ => facet_subset_hyperplane hψ hy))
  · exact Set.singleton_subset_iff.mpr (mem_facet_self Ψ x)

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Every actual building special point is a vertex, provided its apartment
roots satisfy the rank-zero-compatible affine-root-system axioms. -/
theorem isVertex_of_isSpecialPoint
    (hRoots : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    {y : B.ReducedBuilding} (hy : B.IsSpecialPoint y) : B.IsVertex y := by
  obtain ⟨g, x, hxy, hx⟩ := hy
  exact ⟨g, x, hxy, AffineRootSystem.isVertex_of_isSpecialPoint hRoots hx⟩

/-- Regard the supplied actual special point as a special vertex, preserving
its point in the original quotient. -/
def specialVertex
    (hRoots : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (y : B.ReducedBuilding) (hy : B.IsSpecialPoint y) :
    {z : B.ReducedBuilding // B.IsVertex z ∧ B.IsSpecialPoint z} :=
  ⟨y, B.isVertex_of_isSpecialPoint hRoots hy, hy⟩

@[simp]
theorem coe_specialVertex
    (hRoots : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (y : B.ReducedBuilding) (hy : B.IsSpecialPoint y) :
    (B.specialVertex hRoots y hy : B.ReducedBuilding) = y :=
  rfl

end ValuationBuildingData

end Langlands.Geometry.Building
