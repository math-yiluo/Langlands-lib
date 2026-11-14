import Langlands.Geometry.Building.IntegerValuationBuildingData

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- The pointwise fixer of a subset of the reduced building stabilizes it. -/
theorem smul_image_eq_of_mem_pointwiseFixer {Y : Set B.ReducedBuilding}
    {g : rationalPoints G} (hg : g ∈ B.pointwiseFixer Y) : (g • ·) '' Y = Y := by
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer] at hg
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show g • z ∈ Y
    rw [hg z hz]
    exact hz
  · intro hy
    exact ⟨y, hy, hg y hy⟩

end IntegerValuationBuildingData

end Langlands.Geometry.Building
