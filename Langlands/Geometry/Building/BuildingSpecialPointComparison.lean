import Langlands.Geometry.Building.KPBuilding
import Langlands.Geometry.Building.NormalizerAffineRootAction

/-! # Specialness in the building and in its defining apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Specialness of an apartment point is reflected by its building image,
without any apartment-axiom hypothesis. -/
theorem isSpecialBuildingPoint_apartmentMap_iff (x : D.Apartment) :
    D.IsSpecialBuildingPoint (D.apartmentMap x) ↔
      AffineRootSystem.IsSpecialPoint D.affineRoots x := by
  constructor
  · rintro ⟨g, y, hgy, hy⟩
    change ApartmentQuotient.mk D.sharpFixerFamily (g * 1, y) =
      ApartmentQuotient.mk D.sharpFixerFamily (1, x) at hgy
    rw [mul_one] at hgy
    obtain ⟨n, hn, _⟩ := (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily g 1 y x).mp hgy
    rw [← hn]
    exact (AffineRootSystem.isSpecialPoint_apply_iff
      (D.normalizerAffineEquiv_mem_rootStabilizer n) y).mpr hy
  · exact D.isSpecialBuildingPoint_apartmentMap

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building

/-- Internal comparison of specialness for arbitrary apartment data. -/
def BuildingSpecialPointComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (ω : kˣ → ℝ) (D : KPApartmentData i ω) (x : D.Apartment),
    D.IsSpecialBuildingPoint (D.apartmentMap x) ↔
      AffineRootSystem.IsSpecialPoint D.affineRoots x

/-- The comparison is a direct consequence of the quotient relation. -/
theorem buildingSpecialPointComparison : BuildingSpecialPointComparisonStatement.{u} := by
  intro k _ S G i _ _ ω D x
  exact D.isSpecialBuildingPoint_apartmentMap_iff x

end Langlands.Geometry.Building
