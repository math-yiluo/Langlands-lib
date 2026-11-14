import Langlands.Geometry.Building.ApartmentQuotientRootDistance
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof

/-! # The invariant root distance on every supplied maximal-unramified building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H)

local instance : Fintype (relativeRoots B.i) := by
  let := B.isConnectedReductive.smooth
  exact (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).fintype

/-- The intrinsic root distance on the original quotient. Common-apartment coverage
and finiteness of the actual roots are theorems for the supplied building data. -/
def invariantRootDistance (x y : B.ReducedBuilding) : ℝ :=
  B.apartment.chosenRootDistance (commonApartments F H B) x y

/-- The existing rational-point action preserves the intrinsic root distance. -/
theorem invariantRootDistance_smul (g : rationalPoints H) (x y : B.ReducedBuilding) :
    B.invariantRootDistance (g • x) (g • y) = B.invariantRootDistance x y := by
  exact B.apartment.chosenRootDistance_smul B.isConnectedReductive B.isMaximalSplitTorus
    (commonApartments F H B) g x y

/-- Every translated original apartment realizes the prescribed root distance. -/
theorem invariantRootDistance_smul_apartmentMap (g : rationalPoints H)
    (a b : B.Apartment) :
    B.invariantRootDistance (g • B.apartmentMap a) (g • B.apartmentMap b) =
      Real.sqrt (∑ᶠ α : relativeRoots B.i, rootForm B.i α (a -ᵥ b) ^ 2) := by
  exact B.apartment.chosenRootDistance_smul_apartmentMap_eq_sqrt B.isConnectedReductive
    B.isMaximalSplitTorus (commonApartments F H B) g a b

/-- The original apartment has exactly its prescribed root distance. -/
theorem invariantRootDistance_apartmentMap (a b : B.Apartment) :
    B.invariantRootDistance (B.apartmentMap a) (B.apartmentMap b) =
      Real.sqrt (∑ᶠ α : relativeRoots B.i, rootForm B.i α (a -ᵥ b) ^ 2) := by
  simpa only [one_smul] using B.invariantRootDistance_smul_apartmentMap 1 a b

/-- Invariance and the original-apartment formula determine the distance uniquely. -/
theorem eq_invariantRootDistance_of_invariant
    (d : B.ReducedBuilding → B.ReducedBuilding → ℝ)
    (hsmul : ∀ (g : rationalPoints H) (x y : B.ReducedBuilding),
      d (g • x) (g • y) = d x y)
    (hapt : ∀ a b : B.Apartment,
      d (B.apartmentMap a) (B.apartmentMap b) = Real.sqrt (∑ᶠ α : relativeRoots B.i, rootForm B.i α (a -ᵥ b) ^ 2)) :
    d = B.invariantRootDistance := by
  funext x y
  obtain ⟨g, a, b, rfl, rfl⟩ := commonApartments F H B x y
  exact (hsmul g _ _).trans
    ((hapt a b).trans (B.invariantRootDistance_smul_apartmentMap g a b).symm)

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
