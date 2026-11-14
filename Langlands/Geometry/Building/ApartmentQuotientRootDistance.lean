import Langlands.Geometry.Building.GenericApartmentPairNormalizer
import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.IntegerValuationCommonApartments

/-! # The invariant root-distance function on the original apartment quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- Coordinates of two points in one translated copy of the original apartment. -/
structure PairApartmentCoordinates (x y : D.ReducedBuilding) where
  translate : rationalPoints G
  first : D.Apartment
  second : D.Apartment
  first_eq : translate • D.apartmentMap first = x
  second_eq : translate • D.apartmentMap second = y

/-- Choose common-apartment coordinates using the supplied coverage property. -/
def commonApartmentCoordinates (hcommon : D.HasCommonApartments)
    (x y : D.ReducedBuilding) : D.PairApartmentCoordinates x y :=
  Classical.choice (by
    obtain ⟨g, a, b, ha, hb⟩ := hcommon x y
    exact ⟨⟨g, a, b, ha, hb⟩⟩)

variable [Fintype (relativeRoots i)]

local instance : NormedAddCommGroup (TranslationSpace i) :=
  RootTranslationMetric.normedAddCommGroup i

/-- The root norm of the displacement of chosen common-apartment coordinates.
Its independence of coordinates and invariance are proved below. -/
def chosenRootDistance (hcommon : D.HasCommonApartments)
    (x y : D.ReducedBuilding) : ℝ :=
  let c := D.commonApartmentCoordinates hcommon x y
  ‖(c.first -ᵥ c.second : TranslationSpace i)‖

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hcommon : D.HasCommonApartments)

include hG hi

/-- Every translated original apartment has exactly the canonical displacement
norm, regardless of the coordinates chosen to define the function. -/
theorem chosenRootDistance_smul_apartmentMap (g : rationalPoints G) (a b : D.Apartment) :
    D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b) =
      ‖(a -ᵥ b : TranslationSpace i)‖ := by
  let c := D.commonApartmentCoordinates hcommon
    (g • D.apartmentMap a) (g • D.apartmentMap b)
  have ha : (g⁻¹ * c.translate) • D.apartmentMap c.first = D.apartmentMap a := by
    rw [mul_smul, c.first_eq, inv_smul_smul]
  have hb : (g⁻¹ * c.translate) • D.apartmentMap c.second = D.apartmentMap b := by
    rw [mul_smul, c.second_eq, inv_smul_smul]
  exact (D.norm_vsub_eq_of_two_apartmentMap_eq hG hi (g⁻¹ * c.translate)
    c.first c.second a b ha hb).symm

/-- The distance function realizes the canonical root norm on the original apartment. -/
theorem chosenRootDistance_apartmentMap (a b : D.Apartment) :
    D.chosenRootDistance hcommon (D.apartmentMap a) (D.apartmentMap b) =
      ‖(a -ᵥ b : TranslationSpace i)‖ := by
  simpa only [one_smul] using D.chosenRootDistance_smul_apartmentMap hG hi hcommon 1 a b

/-- The original rational-point action preserves the chosen distance function. -/
theorem chosenRootDistance_smul (h : rationalPoints G) (x y : D.ReducedBuilding) :
    D.chosenRootDistance hcommon (h • x) (h • y) =
      D.chosenRootDistance hcommon x y := by
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  change D.chosenRootDistance hcommon (h • g • D.apartmentMap a)
    (h • g • D.apartmentMap b) =
      D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b)
  rw [← mul_smul, ← mul_smul,
    D.chosenRootDistance_smul_apartmentMap hG hi hcommon,
    D.chosenRootDistance_smul_apartmentMap hG hi hcommon]

/-- The translated chart formula in terms of the actual squared root evaluations. -/
theorem chosenRootDistance_smul_apartmentMap_eq_sqrt
    (g : rationalPoints G) (a b : D.Apartment) :
    D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b) =
      Real.sqrt (∑ᶠ α : relativeRoots i, rootForm i α (a -ᵥ b) ^ 2) := by
  rw [D.chosenRootDistance_smul_apartmentMap hG hi hcommon,
    finsum_eq_sum_of_fintype, ← RootTranslationMetric.norm_sq i (a -ᵥ b),
    Real.sqrt_sq (norm_nonneg _)]

omit hG hi in
theorem chosenRootDistance_nonneg (x y : D.ReducedBuilding) :
    0 ≤ D.chosenRootDistance hcommon x y :=
  norm_nonneg _

theorem chosenRootDistance_comm (x y : D.ReducedBuilding) :
    D.chosenRootDistance hcommon x y = D.chosenRootDistance hcommon y x := by
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  change D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b) =
    D.chosenRootDistance hcommon (g • D.apartmentMap b) (g • D.apartmentMap a)
  rw [D.chosenRootDistance_smul_apartmentMap hG hi hcommon,
    D.chosenRootDistance_smul_apartmentMap hG hi hcommon, ← neg_vsub_eq_vsub_rev, norm_neg]

theorem chosenRootDistance_self (x : D.ReducedBuilding) :
    D.chosenRootDistance hcommon x x = 0 := by
  obtain ⟨g, a, _, ha, _⟩ := hcommon x x
  rw [← ha]
  change D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap a) = 0
  rw [D.chosenRootDistance_smul_apartmentMap hG hi hcommon, vsub_self, norm_zero]

theorem chosenRootDistance_eq_zero_iff (x y : D.ReducedBuilding) :
    D.chosenRootDistance hcommon x y = 0 ↔ x = y := by
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  change D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b) = 0 ↔
    g • D.apartmentMap a = g • D.apartmentMap b
  rw [D.chosenRootDistance_smul_apartmentMap hG hi hcommon, norm_eq_zero,
    vsub_eq_zero_iff_eq]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact D.apartmentMap_injective hG hi ((MulAction.injective g) h)

/-- Coverage and the translated chart formula determine the function uniquely. -/
theorem eq_chosenRootDistance_of_smul_apartmentMap
    (d : D.ReducedBuilding → D.ReducedBuilding → ℝ)
    (hd : ∀ (g : rationalPoints G) (a b : D.Apartment),
      d (g • D.apartmentMap a) (g • D.apartmentMap b) =
        ‖(a -ᵥ b : TranslationSpace i)‖) :
    d = D.chosenRootDistance hcommon := by
  funext x y
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  change d (g • D.apartmentMap a) (g • D.apartmentMap b) =
    D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b)
  rw [hd, D.chosenRootDistance_smul_apartmentMap hG hi hcommon]

/-- Invariance together with the original-apartment formula also determines the
function uniquely. -/
theorem eq_chosenRootDistance_of_invariant
    (d : D.ReducedBuilding → D.ReducedBuilding → ℝ)
    (hsmul : ∀ (g : rationalPoints G) (x y : D.ReducedBuilding),
      d (g • x) (g • y) = d x y)
    (hapt : ∀ a b : D.Apartment,
      d (D.apartmentMap a) (D.apartmentMap b) = ‖(a -ᵥ b : TranslationSpace i)‖) :
    d = D.chosenRootDistance hcommon :=
  D.eq_chosenRootDistance_of_smul_apartmentMap hG hi hcommon d
    (fun g a b => (hsmul g _ _).trans (hapt a b))

end Langlands.Geometry.Building.KPApartmentData
