import Langlands.Geometry.Building.IntegerValuationBoundedNormalizerOrbit
import Langlands.Geometry.Building.IntegerValuationCommonApartments
import Langlands.Geometry.Building.ApartmentQuotientFactorization
import Langlands.Geometry.Metric.KPBoundedActionFixedPointProof

/-! # Bounded building orbits from common apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))} [v.Compatible]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

private instance boundedBuildingOrbitAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Common apartments and a bounded sharp fixer give a bounded basepoint
orbit for every algebraically bounded subset, in any isometric metric on the
original quotient. -/
theorem isBounded_image_smul_apartmentMap
    [MetricSpace B.ReducedBuilding]
    [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]
    (hcommon : B.apartment.HasCommonApartments)
    (x : B.Apartment)
    (hP : IsAlgebraicallyBounded k G.X
      (B.sharpFixer {x} : Set (rationalPoints G)))
    (X : Set (rationalPoints G)) (hX : IsAlgebraicallyBounded k G.X X) :
    Bornology.IsBounded ((fun g : rationalPoints G => g • B.apartmentMap x) '' X) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let Y : Set (normalizerPoints B.i) :=
    {n | (n : rationalPoints G) ∈
      (B.sharpFixer {x} : Set (rationalPoints G)) * X * B.sharpFixer {x}}
  have hY : IsAlgebraicallyBounded k G.X
      ((fun n : normalizerPoints B.i => (n : rationalPoints G)) '' Y) :=
    (isAlgebraicallyBounded_mul_of_finiteType
      (isAlgebraicallyBounded_mul_of_finiteType hP hX) hP).mono (by
        rintro _ ⟨n, hn, rfl⟩
        exact hn)
  have hfin := (B.finite_normalizer_orbit_of_isAlgebraicallyBounded Y hY x).image
    B.apartmentMap
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (B.apartmentMap x)).mp
    hfin.isBounded
  refine (Metric.isBounded_iff_subset_closedBall (B.apartmentMap x)).mpr ⟨R, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨p, hp, n, q, hq, hgn⟩ :=
    (ApartmentQuotient.hasCommonTranslatedApartment_iff_factorization
      B.apartment.sharpFixerFamily).mp hcommon x x g
  have hnY : n ∈ Y := by
    change (n : rationalPoints G) ∈
      (B.sharpFixer {x} : Set (rationalPoints G)) * X * B.sharpFixer {x}
    refine ⟨p⁻¹ * g, ⟨p⁻¹, inv_mem hp, g, hg, rfl⟩,
      q⁻¹, inv_mem hq, ?_⟩
    rw [hgn]
    group
  have hpx : p • B.apartmentMap x = B.apartmentMap x :=
    B.mem_fixer.mp (B.sharpFixer_le_fixer x hp)
  have hqx : q • B.apartmentMap x = B.apartmentMap x :=
    B.mem_fixer.mp (B.sharpFixer_le_fixer x hq)
  have hnb : dist (B.apartmentMap (n • x)) (B.apartmentMap x) ≤ R :=
    hR ⟨n • x, ⟨n, hnY, rfl⟩, rfl⟩
  change dist (g • B.apartmentMap x) (B.apartmentMap x) ≤ R
  calc
    dist (g • B.apartmentMap x) (B.apartmentMap x) =
        dist (p • ((n : rationalPoints G) • B.apartmentMap x))
          (p • B.apartmentMap x) := by
      rw [hpx, hgn, mul_smul, mul_smul, hqx]
    _ = dist ((n : rationalPoints G) • B.apartmentMap x) (B.apartmentMap x) :=
      dist_smul _ _ _
    _ ≤ R := by
      rw [B.normalizer_smul_apartmentMap]
      exact hnb

/-- The same premises bound the orbit of every quotient point. -/
theorem isBounded_image_smul_of_commonApartments
    [MetricSpace B.ReducedBuilding]
    [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]
    (hcommon : B.apartment.HasCommonApartments)
    (x : B.Apartment)
    (hP : IsAlgebraicallyBounded k G.X
      (B.sharpFixer {x} : Set (rationalPoints G)))
    (X : Set (rationalPoints G)) (hX : IsAlgebraicallyBounded k G.X X)
    (y : B.ReducedBuilding) :
    Bornology.IsBounded ((fun g : rationalPoints G => g • y) '' X) := by
  let : Nonempty B.ReducedBuilding := ⟨y⟩
  exact (Metric.KP.hasBoundedAction_iff_forall (X := B.ReducedBuilding) X).mp
    ⟨B.apartmentMap x, B.isBounded_image_smul_apartmentMap hcommon x hP X hX⟩ y

/-- A supplied complete NPC isometric metric turns the bounded-orbit
conclusion into a fixed point for every algebraically bounded subgroup. -/
theorem exists_fixed_of_commonApartments
    [MetricSpace B.ReducedBuilding] [CompleteSpace B.ReducedBuilding]
    [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]
    (hNPC : Metric.KP.IsNonpositivelyCurved B.ReducedBuilding)
    (hcommon : B.apartment.HasCommonApartments)
    (x : B.Apartment)
    (hP : IsAlgebraicallyBounded k G.X
      (B.sharpFixer {x} : Set (rationalPoints G)))
    (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G))) :
    ∃ y : B.ReducedBuilding, ∀ g ∈ H, g • y = y := by
  let : Nonempty B.ReducedBuilding := ⟨B.apartmentMap x⟩
  let : IsIsometricSMul H B.ReducedBuilding :=
    ⟨fun g => isometry_smul B.ReducedBuilding (g : rationalPoints G)⟩
  have hbound : Metric.KP.HasBoundedAction B.ReducedBuilding (Set.univ : Set H) := by
    refine ⟨B.apartmentMap x, ?_⟩
    apply (B.isBounded_image_smul_apartmentMap hcommon x hP
      (H : Set (rationalPoints G)) hH).subset
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, g.property, rfl⟩
  obtain ⟨y, hy⟩ := Metric.KP.boundedActionFixedPoint B.ReducedBuilding hNPC H hbound
  exact ⟨y, fun g hg => hy ⟨g, hg⟩⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.Geometry.Building.IntegerValuation

/-- Common apartments, a bounded sharp fixer and a supplied complete NPC
isometric metric imply fixed points of algebraically bounded subgroups. -/
def BoundedFixedPointFromCommonApartmentsStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)
    [MetricSpace B.ReducedBuilding] [CompleteSpace B.ReducedBuilding]
    [IsIsometricSMul (rationalPoints G) B.ReducedBuilding],
    Metric.KP.IsNonpositivelyCurved B.ReducedBuilding →
    B.apartment.HasCommonApartments →
    ∀ x : B.Apartment,
      IsAlgebraicallyBounded k G.X (B.sharpFixer {x} : Set (rationalPoints G)) →
      ∀ H : Subgroup (rationalPoints G),
        IsAlgebraicallyBounded k G.X (H : Set (rationalPoints G)) →
        ∃ y : B.ReducedBuilding, ∀ g ∈ H, g • y = y

/-- The finite-normalizer argument followed by the published metric theorem
proves the exact arbitrary-universe conditional fixed-point statement. -/
theorem boundedFixedPointFromCommonApartments :
    BoundedFixedPointFromCommonApartmentsStatement.{u} := by
  intro k _ _ v _ G _ B _ _ _ hNPC hcommon x hP H hH
  exact B.exists_fixed_of_commonApartments hNPC hcommon x hP H hH

end Langlands.Geometry.Building.IntegerValuation
