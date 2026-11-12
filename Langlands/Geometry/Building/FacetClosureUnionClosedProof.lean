import Langlands.Geometry.Building.FacetClosureUnionClosedStatement
import Langlands.Geometry.Building.FacetClosureLipschitz
import Langlands.Geometry.Building.BuildingFacetPartition

/-! # Proof that unions of closed facets of the actual KP quotient are closed -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Every point of the combinatorial closed facet of `p` is a limit of points of the
facet of `p`, along the segment towards `p`. -/
theorem facetClosure_subset_closure_facet (Ψ : Set (P →ᵃ[ℝ] ℝ)) (p : P) :
    facetClosure Ψ p ⊆ closure (facet Ψ p) := by
  intro q hq
  set c : ℝ → P := fun t => AffineMap.lineMap q p t
  have hc : Continuous c := AffineMap.lineMap_continuous
  have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 → c t ∈ facet Ψ p := by
    intro t ht0 ht1 ψ hψ
    have hval : ψ (c t) = (1 - t) * ψ q + t * ψ p := by
      simp only [c, AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
      ring
    show SignType.sign (ψ p) = SignType.sign (ψ (c t))
    rw [hval]
    rcases hq ψ hψ with h0 | hs
    · have hq0 : ψ q = 0 := sign_eq_zero_iff.1 h0
      rw [hq0, mul_zero, zero_add, sign_mul, sign_pos ht0, one_mul]
    · have h1t : 0 ≤ 1 - t := by linarith
      rcases lt_trichotomy (ψ p) 0 with hp | hp | hp
      · have hqn : ψ q < 0 := by
          rw [sign_neg hp] at hs
          exact sign_eq_neg_one_iff.1 hs
        rw [sign_neg hp, sign_neg (by nlinarith)]
      · rw [hp] at hs ⊢
        rw [sign_zero] at hs
        rw [sign_eq_zero_iff.1 hs]
        simp
      · have hqp : 0 < ψ q := by
          rw [sign_pos hp] at hs
          exact sign_eq_one_iff.1 hs
        rw [sign_pos hp, sign_pos (by nlinarith)]
  have hlim : Tendsto c (𝓝[>] 0) (𝓝 q) := by
    have := hc.tendsto 0
    simp only [c, AffineMap.lineMap_apply_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact hmem t ht.1 ht.2.le

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G}

section ApartmentMetric

attribute [local instance] metricRootFintype RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace apartmentMetricSpace apartmentNormedAddTorsor

variable [MetricSpace B.ReducedBuilding] [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]

/-- The first part of KP Lemma 4.2.11 for the existing quotient: every point `x` has a
ball around it such that every facet meeting that ball contains `x` in its closure. -/
theorem exists_forall_isFacet_mem_closure
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hD : B.SatisfiesApartmentAxioms) (hA : Isometry B.apartmentMap)
    (x : B.ReducedBuilding) :
    ∃ ε > 0, ∀ Y : Set B.ReducedBuilding, B.IsFacet Y →
      ∀ y ∈ Y, dist y x < ε → x ∈ closure Y := by
  have := RootTranslationMetric.finiteDimensional B.i
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨g₀, b, rfl⟩ := B.exists_smul_apartmentMap x
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (AffineRootSystem.eventually_mem_facetClosure hΨ.finite_bounded_at b)
  refine ⟨ε, hε, fun Y hY y hyY hyx => ?_⟩
  obtain ⟨Z, ⟨h, rfl⟩, hxZ, hyZ⟩ := hcommon (g₀ • B.apartmentMap b) y
  obtain ⟨_, ⟨a₀, rfl⟩, ha₀⟩ := Set.mem_smul_set.1 hxZ
  obtain ⟨_, ⟨a₁, rfl⟩, ha₁⟩ := Set.mem_smul_set.1 hyZ
  obtain ⟨n, hn⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq
    (g := g₀⁻¹ * h) (a := a₀) (b := b) (by rw [mul_smul, ha₀, inv_smul_smul])
  set h' : rationalPoints G := h * (n : rationalPoints G)⁻¹
  have hchart : ∀ a : B.Apartment, h' • B.apartmentMap (n • a) = h • B.apartmentMap a := by
    intro a
    rw [← B.normalizer_smul_apartmentMap, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hx' : h' • B.apartmentMap b = g₀ • B.apartmentMap b := by
    conv_lhs => rw [← hn]
    rw [hchart, ha₀]
  have hy' : h' • B.apartmentMap (n • a₁) = y := by
    rw [hchart, ha₁]
  have hdist : dist (n • a₁) b < ε := by
    rw [← B.dist_smul_apartmentMap hA h', hy', hx']
    exact hyx
  have hcl : b ∈ AffineRootSystem.facetClosure B.affineRoots (n • a₁) := hball hdist
  set f : B.Apartment → B.ReducedBuilding := fun z => h' • B.apartmentMap z
  have hf : Continuous f := (continuous_const_smul h').comp hA.continuous
  have hYf : Y = f '' AffineRootSystem.facet B.affineRoots (n • a₁) :=
    hY.eq_of_mem_mem B hD ⟨h', _, AffineRootSystem.isFacet_facet _ _, rfl⟩ hyY
      ⟨n • a₁, AffineRootSystem.mem_facet_self _ _, hy'⟩
  rw [← hx', hYf]
  exact image_closure_subset_closure_image hf
    ⟨b, AffineRootSystem.facetClosure_subset_closure_facet _ _ hcl, rfl⟩

end ApartmentMetric

end ValuationBuildingData

open ValuationBuildingData in
/-- KP Theorem 4.2.10, second assertion, for the existing quotient of supplied valuation
building data. -/
theorem facetClosureUnionClosed : FacetClosureUnionClosedStatement.{u} := by
  intro F _ _ _ _ G _ B _ _ hcommon hD hA X hX
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨ε, hε, hfac⟩ := exists_forall_isFacet_mem_closure hcommon hD hA x
  obtain ⟨z, hzM, hxz⟩ := Metric.mem_closure_iff.1 hx ε hε
  obtain ⟨Y, hYX, hzY⟩ := Set.mem_iUnion₂.1 hzM
  obtain ⟨y, hyball, hyY⟩ := mem_closure_iff.1 hzY (Metric.ball x ε) Metric.isOpen_ball
    (by rw [Metric.mem_ball, dist_comm]; exact hxz)
  exact Set.mem_iUnion₂.2 ⟨Y, hYX, hfac Y (hX Y hYX) y hyY (Metric.mem_ball.1 hyball)⟩

end Langlands.Geometry.Building
