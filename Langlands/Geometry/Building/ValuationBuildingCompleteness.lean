import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.AffineRootOrbitDiscreteness
import Langlands.Geometry.Building.ApartmentFixedPointReduction
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Metric.DiscreteOrbitCompleteness

/-! # Completeness of a building metric with isometric apartment charts

KP Theorem 4.2.10 for a metric on the existing quotient `B(G)`: if `G(F)` acts
isometrically, the apartment map `A(S) → B(G)` is an isometry from a proper
metric on `A(S)`, any two points share an apartment, and `N(F)` has discrete
orbits on `A(S)`, then `B(G)` is complete. For the Euclidean root metric of
`ValuationApartmentMetric`, AS 2–AS 5 supply properness and the discreteness of
`N(F)`-orbits.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- If a translate of an apartment point lies in the image of the apartment at
an apartment point, then the two apartment points differ by an element of
`N(F)`. This is the relation (7.6.2) defining the quotient. -/
theorem exists_normalizer_smul_eq_of_smul_apartmentMap_eq {g : rationalPoints G}
    {a b : B.Apartment} (h : g • B.apartmentMap a = B.apartmentMap b) :
    ∃ n : normalizerPoints B.i, n • a = b := by
  have h' : ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, a) =
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := h
  rw [ApartmentQuotient.mk_eq_mk_iff] at h'
  obtain ⟨n, hn, -⟩ := h'
  exact ⟨n, hn⟩

section Metric

variable [MetricSpace B.Apartment] [MetricSpace B.ReducedBuilding]
  [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]

/-- With an isometric apartment map, distances inside a translated apartment
are computed in `A(S)`. -/
theorem dist_smul_apartmentMap (hA : Isometry B.apartmentMap) (h : rationalPoints G)
    (a b : B.Apartment) :
    dist (h • B.apartmentMap a) (h • B.apartmentMap b) = dist a b := by
  rw [dist_smul, hA.dist_eq]

/-- An isometric apartment map makes `N(F)` act isometrically on `A(S)`. -/
theorem dist_normalizer_smul (hA : Isometry B.apartmentMap) (n : normalizerPoints B.i)
    (a b : B.Apartment) : dist (n • a) (n • b) = dist a b := by
  rw [← hA.dist_eq, ← B.normalizer_smul_apartmentMap, ← B.normalizer_smul_apartmentMap,
    dist_smul, hA.dist_eq]

variable {B}

/-- KP Lemma 4.2.11 at a point of the base apartment: discreteness of the
`N(F)`-orbit of `b` in `A(S)` gives discreteness of the `G(F)`-orbit of its
image, using a common apartment of the two points. -/
theorem exists_forall_dist_smul_apartmentMap_lt_imp_eq
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hA : Isometry B.apartmentMap) {b : B.Apartment} {ε : ℝ}
    (hfix : ∀ n : normalizerPoints B.i, dist (n • b) b < ε → n • b = b)
    (g : rationalPoints G) (hg : dist (g • B.apartmentMap b) (B.apartmentMap b) < ε) :
    g • B.apartmentMap b = B.apartmentMap b := by
  obtain ⟨Y, ⟨h, rfl⟩, hbY, hgbY⟩ := hcommon (B.apartmentMap b) (g • B.apartmentMap b)
  obtain ⟨_, ⟨a₁, rfl⟩, ha₁⟩ := Set.mem_smul_set.1 hbY
  obtain ⟨_, ⟨a₂, rfl⟩, ha₂⟩ := Set.mem_smul_set.1 hgbY
  obtain ⟨n₁, hn₁⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq ha₁
  obtain ⟨n₂, hn₂⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq
    (g := g⁻¹ * h) (a := a₂) (b := b) (by rw [mul_smul, ha₂, inv_smul_smul])
  have e₂ : a₂ = n₂⁻¹ • b := by rw [← hn₂, inv_smul_smul]
  have key : dist ((n₁ * n₂⁻¹) • b) b < ε := by
    calc dist ((n₁ * n₂⁻¹) • b) b = dist (n₁ • a₂) (n₁ • a₁) := by
          rw [mul_smul, ← e₂, hn₁]
      _ = dist a₂ a₁ := B.dist_normalizer_smul hA n₁ a₂ a₁
      _ = dist (g • B.apartmentMap b) (B.apartmentMap b) := by
          rw [← B.dist_smul_apartmentMap hA h, ha₂, ha₁]
      _ < ε := hg
  have hfixed := hfix _ key
  rw [mul_smul, ← e₂] at hfixed
  have ha : a₂ = a₁ := smul_left_cancel n₁ (hfixed.trans hn₁.symm)
  rw [← ha₂, ha, ha₁]

/-- KP Lemma 4.2.11: every `G(F)`-orbit in `B(G)` is discrete, in the sense
that a translate closer than some positive radius is equal to the point. -/
theorem exists_forall_dist_smul_lt_imp_eq
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hA : Isometry B.apartmentMap)
    (hdisc : ∀ b : B.Apartment, ∃ ε > 0, ∀ n : normalizerPoints B.i,
      dist (n • b) b < ε → n • b = b)
    (y : B.ReducedBuilding) :
    ∃ ε > 0, ∀ g : rationalPoints G, dist (g • y) y < ε → g • y = y := by
  obtain ⟨g₀, b, rfl⟩ := B.exists_smul_apartmentMap y
  obtain ⟨ε, hε, hfix⟩ := hdisc b
  refine ⟨ε, hε, fun g hg => ?_⟩
  have hconj : g₀ • ((g₀⁻¹ * g * g₀) • B.apartmentMap b) = g • g₀ • B.apartmentMap b := by
    rw [smul_smul, smul_smul]
    congr 1
    group
  have hg' : dist ((g₀⁻¹ * g * g₀) • B.apartmentMap b) (B.apartmentMap b) < ε := by
    rwa [← dist_smul g₀, hconj]
  have h := exists_forall_dist_smul_apartmentMap_lt_imp_eq hcommon hA hfix _ hg'
  rw [← hconj, h]

/-- KP Theorem 4.2.10 for the existing quotient: a metric on `B(G)` for which
`G(F)` acts isometrically and the apartment map is an isometry from a proper
metric on `A(S)` is complete, provided any two points share an apartment and
`N(F)` has discrete orbits on `A(S)`. The compact set covering a unit ball is
the image of a closed unit ball of `A(S)`. -/
theorem completeSpace_of_isometry_apartmentMap [ProperSpace B.Apartment]
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hA : Isometry B.apartmentMap)
    (hdisc : ∀ b : B.Apartment, ∃ ε > 0, ∀ n : normalizerPoints B.i,
      dist (n • b) b < ε → n • b = b) :
    CompleteSpace B.ReducedBuilding := by
  refine Metric.KP.completeSpace_of_discrete_orbits (Γ := rationalPoints G) ?_
    (exists_forall_dist_smul_lt_imp_eq hcommon hA hdisc)
  intro x₀
  obtain ⟨g₀, b, rfl⟩ := B.exists_smul_apartmentMap x₀
  refine ⟨B.apartmentMap '' Metric.closedBall b 1,
    (isCompact_closedBall b 1).image hA.continuous, fun x hx => ?_⟩
  obtain ⟨Y, ⟨h, rfl⟩, hx₀Y, hxY⟩ := hcommon (g₀ • B.apartmentMap b) x
  obtain ⟨_, ⟨a₀, rfl⟩, ha₀⟩ := Set.mem_smul_set.1 hx₀Y
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Set.mem_smul_set.1 hxY
  obtain ⟨n, hn⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq
    (g := g₀⁻¹ * h) (a := a₀) (b := b) (by rw [mul_smul, ha₀, inv_smul_smul])
  refine ⟨h * (n : rationalPoints G)⁻¹, B.apartmentMap (n • a), ⟨n • a, ?_, rfl⟩, ?_⟩
  · rw [Metric.mem_closedBall, ← hn, B.dist_normalizer_smul hA,
      ← B.dist_smul_apartmentMap hA h, ha, ha₀]
    exact hx.le
  · rw [← B.normalizer_smul_apartmentMap, mul_smul, inv_smul_smul, ha]

end Metric

section ApartmentMetric

attribute [local instance] metricRootFintype RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace apartmentMetricSpace apartmentNormedAddTorsor

/-- The Euclidean root metric on `A(S)` is proper. -/
theorem apartment_properSpace : ProperSpace B.Apartment := by
  have := RootTranslationMetric.finiteDimensional B.i
  let e := IsometryEquiv.vaddConst (Classical.arbitrary B.Apartment)
  exact e.isometry.antilipschitzWith.properSpace e.continuous e.surjective

/-- The apartment step of KP Lemma 4.2.11 for the Euclidean root metric: under
AS 2–AS 5 the `N(F)`-orbits in `A(S)` are discrete, because `N(F)` acts through
`W(Ψ)ᵉˣᵗ`, which permutes the locally finite affine root system `Ψ`. -/
theorem exists_forall_dist_normalizer_smul_lt_imp_eq (hD : B.SatisfiesApartmentAxioms)
    (b : B.Apartment) :
    ∃ ε > 0, ∀ n : normalizerPoints B.i, dist (n • b) b < ε → n • b = b := by
  have := RootTranslationMetric.finiteDimensional B.i
  obtain ⟨ε, hε, h⟩ := AffineRootSystem.exists_forall_dist_lt_imp_eq
    hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement b
  exact ⟨ε, hε, fun n hn => h _ (AffineRootSystem.extendedAffineWeylGroup_le_rootStabilizer _
    (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩)) hn⟩

variable {B}

/-- KP Theorem 4.2.10 for a metric on `B(G)` extending the Euclidean root metric
of `A(S)`: if `G(F)` acts isometrically, the apartment map is an isometry, any
two points share an apartment and AS 2–AS 5 hold, then `B(G)` is complete. -/
theorem completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms
    [MetricSpace B.ReducedBuilding] [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hD : B.SatisfiesApartmentAxioms) (hA : Isometry B.apartmentMap) :
    CompleteSpace B.ReducedBuilding :=
  haveI := B.apartment_properSpace
  completeSpace_of_isometry_apartmentMap hcommon hA
    (B.exists_forall_dist_normalizer_smul_lt_imp_eq hD)

end ApartmentMetric

end Langlands.Geometry.Building.ValuationBuildingData
