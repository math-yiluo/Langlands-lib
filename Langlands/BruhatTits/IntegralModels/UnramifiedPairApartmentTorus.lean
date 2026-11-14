import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.BruhatTits.IntegralModels.UnramifiedIntegralRoots
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # A common apartment and its integral torus in a pair-fixer model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section General

variable {K : Type u} [Field K]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Bounded points of a conjugated apartment torus fix every point of
that translated apartment and belong to the ambient character kernel. -/
theorem map_translatedApartmentTorus_kernel_le_oneFixer
    (q : rationalPoints G) (Y : Set B.ReducedBuilding)
    (hY : Y ⊆ Set.range (fun x : B.Apartment => q • B.apartmentMap x)) :
    (characterValuationKernel v B.S.toGrp).map
        (rationalPoints.map (B.i ≫ (G.innerIso q).hom)) ≤
      characterValuationKernel v G ⊓ B.pointwiseFixer Y := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨IntegerValuation.map_mem_characterValuationKernel v _ ht, ?_⟩
  apply B.apartment.mem_pointwiseFixer.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hY hy
  have hfix := B.apartment.map_torusUnits_smul_apartmentMap v B.centralizer
    B.isOmegaCompatible (𝟙 B.S) t ht x
  change rationalPoints.map ((𝟙 B.S.toGrp) ≫ B.i) t • B.apartmentMap x =
    B.apartmentMap x at hfix
  simp only [Category.id_comp] at hfix
  rw [rationalPoints.map_comp_apply, rationalPoints_map_innerIso]
  change (q * rationalPoints.map B.i t * q⁻¹) • (q • B.apartmentMap x) =
    q • B.apartmentMap x
  simp only [mul_smul, inv_smul_smul, hfix]

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (B : MaximalUnramified.BuildingData F G)
  (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
  (y₁ y₂ : B.ReducedBuilding)

/-- An actual common translated apartment for a pair, together with a
closed integral split torus whose generic inclusion is its conjugated torus. -/
structure PairApartmentTorusData where
  translatingPoint : rationalPoints G
  firstCoordinate : B.Apartment
  secondCoordinate : B.Apartment
  first_eq : translatingPoint • B.apartmentMap firstCoordinate = y₁
  second_eq : translatingPoint • B.apartmentMap secondCoordinate = y₂
  integralTorus : IntegralSplitTorusData N (B.i ≫ (G.innerIso translatingPoint).hom)
  isClosed : IsClosedSubgroup integralTorus.inclusion

/-- A pair-fixer model contains the actual closed integral split torus of
some common translated apartment for its endpoints. -/
theorem exists_pairApartmentTorusData
    (hN : characterValuationKernel (MaximalUnramified.valuation F) G ⊓
      B.pointwiseFixer {y₁, y₂} ≤ N.integralPoints) :
    Nonempty (PairApartmentTorusData B N y₁ y₂) := by
  obtain ⟨q, x₁, x₂, hx₁, hx₂⟩ := MaximalUnramified.commonApartments F G B y₁ y₂
  have hY : ({y₁, y₂} : Set B.ReducedBuilding) ⊆
      Set.range (fun x : B.Apartment => q • B.apartmentMap x) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨x₁, hx₁⟩
    · exact Set.mem_singleton_iff.mp hy ▸ ⟨x₂, hx₂⟩
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have hv : ∀ a : (fixedFieldIntegers F)ˣ,
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 := by
    intro a
    have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
    have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
      (h.trans (map_one (fixedFieldValuation F)).symm)
    simpa only [map_one] using h'
  have hmax := B.isMaximalSplitTorus.comp_iso (G.innerIso q)
  obtain ⟨T, j, e, hT, hj, hcomm⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      N (MaximalUnramified.valuation F) hv (B.i ≫ (G.innerIso q).hom)
      hmax.1.1 hmax.1.2
      ((map_translatedApartmentTorus_kernel_le_oneFixer B q {y₁, y₂} hY).trans hN)
  exact ⟨⟨q, x₁, x₂, hx₁, hx₂, ⟨T, hT, j, e, hcomm⟩, hj⟩⟩

/-- Choose the common apartment and its compatible closed integral torus
from the actual pair-fixer inclusion. -/
def unramifiedPairApartmentTorusData
    (hN : characterValuationKernel (MaximalUnramified.valuation F) G ⊓
      B.pointwiseFixer {y₁, y₂} ≤ N.integralPoints) :
    PairApartmentTorusData B N y₁ y₂ :=
  Classical.choice (exists_pairApartmentTorusData B N y₁ y₂ hN)

/-- The prescribed generic conjugated torus is maximal split in the
actual generic ambient group. -/
theorem PairApartmentTorusData.generic_isMaximalSplitTorus
    (A : PairApartmentTorusData B N y₁ y₂) :
    IsMaximalSplitTorus (B.i ≫ (G.innerIso A.translatingPoint).hom) :=
  B.isMaximalSplitTorus.comp_iso (G.innerIso A.translatingPoint)

end Unramified

end Langlands.BruhatTits.IntegralModels
