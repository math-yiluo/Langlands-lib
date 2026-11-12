import Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionStatement
import Langlands.Geometry.Building.MetricRealizationProof
import Langlands.Geometry.Metric.KPGeodesicUniquenessProof
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Apartment conjugacy fixing the intersection

KP Proposition 4.2.24 for the supplied quotient building. Convexity follows
from the explicit NPC metric; a maximal common kernel replaces the source
proof's choice of a maximal-dimensional facet.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open AffineRootSystem AffineRootSystem.GalleryGeometry

/-- A convex set has a point whose vanishing roots vanish on the entire set. -/
private theorem exists_maximal_facet_zero
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    [FiniteDimensional ℝ V] {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {C : Set A} (hne : C.Nonempty)
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t • (y -ᵥ x) +ᵥ x ∈ C) :
    ∃ x ∈ C, ∀ ψ ∈ Ψ, ψ x = 0 → ∀ y ∈ C, ψ y = 0 := by
  classical
  let D : A → Submodule ℝ V := fun x =>
    ⨅ (ψ : A →ᵃ[ℝ] ℝ) (_ : ψ ∈ Ψ) (_ : ψ x = 0), LinearMap.ker ψ.linear
  have memD (x : A) (v : V) : v ∈ D x ↔ ∀ ψ ∈ Ψ, ψ x = 0 → ψ.linear v = 0 := by
    simp only [D, Submodule.mem_iInf, LinearMap.mem_ker]
  let S : Set ℕ := (fun x => Module.finrank ℝ (D x)) '' C
  have hSf : S.Finite := (Set.finite_Iic (Module.finrank ℝ V)).subset (by
    rintro n ⟨x, -, rfl⟩
    exact Submodule.finrank_le _)
  have hSne : S.Nonempty := hne.image _
  obtain ⟨x, hx, hxrank⟩ := hSne.csSup_mem hSf
  change Module.finrank ℝ (D x) = sSup S at hxrank
  have hmax (z : A) (hz : z ∈ C) : Module.finrank ℝ (D z) ≤ Module.finrank ℝ (D x) := by
    rw [hxrank]
    exact le_csSup hSf.bddAbove ⟨z, hz, rfl⟩
  refine ⟨x, hx, ?_⟩
  intro ψ hψ hψx y hy
  have hev := (eventually_sign_smul_vadd hΨ x (y -ᵥ x)).and
    (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from eventually_lt_nhds (by norm_num))
  obtain ⟨t, ht, hs, ht1⟩ := exists_pos_of_eventually hev
  let z := t • (y -ᵥ x) +ᵥ x
  have hz : z ∈ C := hC x hx y hy t ht.le ht1.le
  have hzroot (rho : A →ᵃ[ℝ] ℝ) (hrho : rho ∈ Ψ) (hrhoz : rho z = 0) :
      rho x = 0 ∧ rho y = 0 := by
    have hrhox : rho x = 0 := by
      by_contra hn
      have hsign := hs rho hrho hn
      rw [show rho (t • (y -ᵥ x) +ᵥ x) = 0 from hrhoz] at hsign
      rw [sign_zero, eq_comm, sign_eq_zero_iff] at hsign
      exact hn hsign
    have heq := hrhoz
    dsimp [z] at heq
    rw [apply_smul_vadd, hrhox, zero_add] at heq
    have hlin := (mul_eq_zero.mp heq).resolve_left ht.ne'
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hrhox, sub_zero] at hlin
    exact ⟨hrhox, hlin⟩
  have hle : D x ≤ D z := by
    intro v hv
    rw [memD] at hv ⊢
    exact fun rho hrho hrhoz => hv rho hrho (hzroot rho hrho hrhoz).1
  have heq : D x = D z := Submodule.eq_of_le_of_finrank_le hle (hmax z hz)
  have hv : y -ᵥ x ∈ D z := by
    rw [memD]
    intro rho hrho hrhoz
    obtain ⟨hrhox, hrhoy⟩ := hzroot rho hrho hrhoz
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hrhox, hrhoy, sub_self]
  rw [← heq, memD] at hv
  have hlin := hv ψ hψ hψx
  rwa [AffineMap.linearMap_vsub, vsub_eq_sub, hψx, sub_zero] at hlin

/-- The facet at the selected point determines affine automorphisms on the set. -/
private theorem exists_facet_fixer_controls_convex
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    [FiniteDimensional ℝ V] {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {C : Set A} (hne : C.Nonempty)
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t • (y -ᵥ x) +ᵥ x ∈ C) :
    ∃ x ∈ C, ∀ e : A ≃ᵃ[ℝ] A, (∀ z ∈ facet Ψ x, e z = z) →
      ∀ y ∈ C, e y = y := by
  obtain ⟨x, hx, hzero⟩ := exists_maximal_facet_zero hΨ hne hC
  refine ⟨x, hx, ?_⟩
  intro e he y hy
  have hex : e x = x := he x (mem_facet_self _ _)
  obtain ⟨t, ht, hs⟩ := exists_pos_of_eventually (eventually_sign_smul_vadd hΨ x (y -ᵥ x))
  have hmem : t • (y -ᵥ x) +ᵥ x ∈ facet Ψ x := by
    intro ψ hψ
    by_cases hψx : ψ x = 0
    · rw [apply_smul_vadd, AffineMap.linearMap_vsub, vsub_eq_sub,
        hψx, hzero ψ hψ hψx y hy]
      simp
    · exact (hs ψ hψ hψx).symm
  have hfix := he _ hmem
  rw [AffineEquiv.map_vadd, hex] at hfix
  have hlin := vadd_right_cancel x hfix
  rw [map_smul] at hlin
  have hv := smul_right_injective V ht.ne' hlin
  rw [← vsub_vadd y x, AffineEquiv.map_vadd, hv, hex]

/-- Common points of isometric affine charts have a common straight segment. -/
private theorem lineMap_mem_range_of_isometries
    {V A X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace A] [NormedAddTorsor V A] [MetricSpace X]
    (hX : Metric.KP.IsNonpositivelyCurved X) {e f : A → X}
    (he : Isometry e) (hf : Isometry f) {x y : A}
    (hx : e x ∈ Set.range f) (hy : e y ∈ Set.range f)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    e (AffineMap.lineMap x y t) ∈ Set.range f := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hab : dist x y = dist a b := by
    rw [← he.dist_eq, ← ha, ← hb, hf.dist_eq]
  have hleft : dist (e x) (e (AffineMap.lineMap x y t)) =
      dist (e x) (f (AffineMap.lineMap a b t)) := by
    rw [he.dist_eq, ← ha, hf.dist_eq, dist_left_lineMap, dist_left_lineMap, hab]
  have hright : dist (e (AffineMap.lineMap x y t)) (e y) =
      dist (f (AffineMap.lineMap a b t)) (e y) := by
    rw [he.dist_eq, ← hb, hf.dist_eq, dist_lineMap_right, dist_lineMap_right, hab]
  have hsum : dist (e x) (e (AffineMap.lineMap x y t)) +
      dist (e (AffineMap.lineMap x y t)) (e y) = dist (e x) (e y) := by
    rw [he.dist_eq, he.dist_eq, he.dist_eq, dist_left_lineMap, dist_lineMap_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
    ring
  exact ⟨AffineMap.lineMap a b t,
    (Metric.KP.eq_of_dist_eq_of_dist_add_eq hX hleft hright hsum).symm⟩

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

local instance : Fintype (relativeRoots P.i) := P.toValuationBuildingData.metricRootFintype
local instance : NormedAddCommGroup (TranslationSpace P.i) :=
  RootTranslationMetric.normedAddCommGroup P.i
local instance : NormedSpace ℝ (TranslationSpace P.i) := RootTranslationMetric.normedSpace P.i
local instance : FiniteDimensional ℝ (TranslationSpace P.i) := RootTranslationMetric.finiteDimensional P.i
local instance : MetricSpace P.Apartment := P.toValuationBuildingData.apartmentMetricSpace
local instance : NormedAddTorsor (TranslationSpace P.i) P.Apartment :=
  P.toValuationBuildingData.apartmentNormedAddTorsor

/-- Move an apartment to the base apartment while fixing their intersection. -/
private theorem exists_zero_smul_base_fixing_intersection
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (hconvex : ∀ x, P.apartmentMap x ∈ Y → ∀ y, P.apartmentMap y ∈ Y →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → P.apartmentMap (t • (y -ᵥ x) +ᵥ x) ∈ Y) :
    ∃ r : rationalPoints G, r ∈ P.zeroSubgroup ∧ r • Y = P.apartmentImage ∧
      ∀ z ∈ P.apartmentImage ∩ Y, r • z = z := by
  classical
  let C : Set P.Apartment := P.apartmentMap ⁻¹' Y
  by_cases hne : C.Nonempty
  · have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
    obtain ⟨x, hx, hcontrol⟩ := exists_facet_fixer_controls_convex hΨ hne hconvex
    obtain ⟨r, hr0, hrfix, hrY⟩ := P.exists_zero_forall_mem_facet_smul_eq hD x hY hx
    refine ⟨r, hr0, hrY, ?_⟩
    rintro z ⟨⟨y, rfl⟩, hy⟩
    have hFA (a : P.Apartment) : (P.apartmentBuildingFacet a).val ⊆ P.apartmentImage := by
      rintro _ ⟨b, -, rfl⟩
      exact ⟨b, rfl⟩
    have hFY (a : P.Apartment) (ha : P.apartmentMap a ∈ Y) :
        (P.apartmentBuildingFacet a).val ⊆ Y :=
      hA.subset_of_inter_nonempty hY (P.apartmentBuildingFacet a).property
        ⟨_, ⟨a, mem_facet_self _ _, rfl⟩, ha⟩
    obtain ⟨k, hkF, hkD, hkY⟩ := hT.exists_twoFacet_smul_apartment_eq hY
      P.toValuationBuildingData.isApartment_apartmentImage
      (P.apartmentBuildingFacet x) (P.apartmentBuildingFacet y)
      (hFY x hx) (hFY y hy) (hFA x) (hFA y)
    have hkfix : ∀ b ∈ facet P.affineRoots x,
        (k : rationalPoints G) • P.apartmentMap b = P.apartmentMap b := fun b hb =>
      P.facetZeroStabilizer_smul_eq hD hN hA hT _ k hkF ⟨b, hb, rfl⟩
    have hky : (k : rationalPoints G) • P.apartmentMap y = P.apartmentMap y :=
      P.facetZeroStabilizer_smul_eq hD hN hA hT _ k hkD ⟨y, mem_facet_self _ _, rfl⟩
    set m := r * (k : rationalPoints G)⁻¹ with hm_def
    have hmA : m • P.apartmentImage = P.apartmentImage := by
      calc m • P.apartmentImage = r • ((k : rationalPoints G)⁻¹ • P.apartmentImage) :=
            mul_smul _ _ _
        _ = r • Y := by rw [← hkY, inv_smul_smul]
        _ = P.apartmentImage := hrY
    have hm : m ∈ normalizerPoints P.i :=
      (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
        P.toValuationBuildingData hN m).mp hmA
    let n : normalizerPoints P.i := ⟨m, hm⟩
    have hmz : ∀ b : P.Apartment, m • P.apartmentMap b = P.apartmentMap (n • b) :=
      fun b => P.normalizer_smul_apartmentMap n b
    have hnfix : ∀ b ∈ facet P.affineRoots x,
        P.toValuationBuildingData.normalizerAction n b = b := by
      intro b hb
      apply hA.injective
      rw [ValuationBuildingData.normalizerAction_apply, ← hmz, hm_def, mul_smul,
        inv_smul_eq_iff.mpr (hkfix b hb).symm, hrfix b hb]
    have hny := hcontrol (P.toValuationBuildingData.normalizerAction n) hnfix y hy
    have hmy : m • P.apartmentMap y = P.apartmentMap y := by
      rw [hmz, ← ValuationBuildingData.normalizerAction_apply, hny]
    calc r • P.apartmentMap y = m • ((k : rationalPoints G) • P.apartmentMap y) := by
          rw [hm_def, mul_smul, inv_smul_smul]
      _ = P.apartmentMap y := by rw [hky, hmy]
  · obtain ⟨r, hrY⟩ := hT.exists_zero_smul_apartmentImage hY
    refine ⟨r, r.property, hrY, ?_⟩
    rintro z ⟨⟨y, rfl⟩, hy⟩
    exact (hne ⟨y, hy⟩).elim

end ParahoricBuildingData

attribute [local instance] ValuationBuildingData.metricRootFintype
  RootTranslationMetric.normedAddCommGroup RootTranslationMetric.normedSpace
  ValuationBuildingData.apartmentMetricSpace ValuationBuildingData.apartmentNormedAddTorsor

/-- KP Proposition 4.2.24, including disjoint apartments, under precisely the
seven hypotheses of the published statement. -/
theorem apartmentConjugacyFixingIntersection : ApartmentConjugacyFixingIntersectionStatement.{u} := by
  intro F _ _ _ _ G _ P R T hR _hB _hT _hRR hD hA hTits
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨y, hy, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary P.Apartment)
  obtain ⟨W, _, π, Sgen, hTy⟩ := hTits _ ⟨y, hy, rfl⟩
  have hN := hR.normalizerApartmentStabilizer
  have hK := hR.isBuilding
  let d := P.toValuationBuildingData.buildingDist R hK
  have hd : P.toValuationBuildingData.IsRetractionBuildingDistance d :=
    { smul := P.buildingDist_smul hD hN hA hTy R hK
      apartmentMap := P.buildingDist_apartmentMap hD hN hA hTy R hK
      exists_retraction := P.exists_apartmentRetraction
        (R.hasCommonApartmentWith_of_isBuilding hK) hD hN hA hTits
        (P.buildingDist_translatedApartmentMap hD hN hA hTy R hK) }
  have hglue := hd.isRetractionGluedDistance (R.hasCommonApartmentWith_of_isBuilding hK)
  let := hglue.metricSpace
  have hbase : ∀ Y : Set P.ReducedBuilding, P.IsApartment Y →
      ∃ r : rationalPoints G, r ∈ P.zeroSubgroup ∧ r • Y = P.apartmentImage ∧
        ∀ z ∈ P.apartmentImage ∩ Y, r • z = z := by
    intro Y hY
    apply P.exists_zero_smul_base_fixing_intersection hD hN hA hTy hY
    obtain ⟨g, rfl⟩ := hY
    intro x hx z hz t ht ht1
    rw [ValuationBuildingData.apartmentImage, Set.smul_set_range] at hx hz ⊢
    exact lineMap_mem_range_of_isometries hglue.isNonpositivelyCurved
      (Isometry.of_dist_eq hd.apartmentMap) (Isometry.of_dist_eq (hd.smul_apartmentMap g))
      hx hz ht ht1
  intro A₁ A₂ hA₁ hA₂
  obtain ⟨t, htA⟩ := hTy.exists_zero_smul_apartmentImage hA₁
  obtain ⟨r, hr0, hrA, hrfix⟩ := hbase ((t : rationalPoints G) • A₂)
    (ValuationBuildingData.IsApartment.smul _ hA₂ (t : rationalPoints G))
  refine ⟨(t : rationalPoints G)⁻¹ * r⁻¹ * (t : rationalPoints G),
    P.zeroSubgroup.mul_mem (P.zeroSubgroup.mul_mem (P.zeroSubgroup.inv_mem t.property)
      (P.zeroSubgroup.inv_mem hr0)) t.property, ?_, ?_⟩
  · rw [mul_smul, mul_smul, htA, ← hrA, inv_smul_smul, inv_smul_smul]
  · intro z hz
    have htz : (t : rationalPoints G) • z ∈ P.apartmentImage ∩ (t : rationalPoints G) • A₂ :=
      ⟨htA ▸ Set.smul_mem_smul_set hz.1, Set.smul_mem_smul_set hz.2⟩
    have hfix := hrfix _ htz
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hfix.symm, inv_smul_smul]

end Langlands.Geometry.Building
