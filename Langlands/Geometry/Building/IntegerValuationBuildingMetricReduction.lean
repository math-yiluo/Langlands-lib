import Langlands.Geometry.Building.IntegerValuationCommonApartments
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Metric.RetractionGluing
import Langlands.Geometry.Metric.DiscreteOrbitCompleteness
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.IntegerRootReflections
import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.AffineRootOrbitDiscreteness

/-! # Complete NPC metrics from retractions on integer-valued buildings

The generic metric construction on a supplied integer-valued root-valuation
quotient, extracted from `UnramifiedBuildingMetricReduction` so that it can be
used independently of descent and special-torus statements. All existing public
Lean names, statements, and proofs are retained.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The Euclidean root distance between two apartment points: the square root of
the sum, over the actual relative roots `a`, of `a(x - y)²`. The relative roots
form a finite set for a maximal split torus of a reductive group, so the sum is an
ordinary finite sum there. -/
def rootDistance (x y : D.Apartment) : ℝ :=
  Real.sqrt (∑ᶠ α : relativeRoots i, rootForm i α (x -ᵥ y) ^ 2)

end KPApartmentData

/-! ### The Euclidean root metric on a supplied integer-valued apartment -/

section RootMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Finiteness of the actual relative roots of the supplied maximal split torus. -/
@[instance_reducible]
def rootDistanceFintype : Fintype (relativeRoots B.i) := by
  letI := B.isConnectedReductive.smooth
  exact (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).fintype

attribute [local instance] rootDistanceFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : InnerProductSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.innerProductSpace B.i

/-- The Euclidean root metric on the supplied apartment. -/
abbrev rootMetricSpace : MetricSpace B.Apartment :=
  metricSpaceOfNormedAddCommGroupOfAddTorsor (TranslationSpace B.i) B.Apartment

attribute [local instance] rootMetricSpace

/-- The supplied affine structure is a normed torsor for the root metric. -/
abbrev rootNormedAddTorsor : NormedAddTorsor (TranslationSpace B.i) B.Apartment where
  dist_eq_norm' _ _ := rfl

attribute [local instance] rootNormedAddTorsor

theorem root_dist_eq_norm (x y : B.Apartment) :
    dist x y = ‖(x -ᵥ y : TranslationSpace B.i)‖ := rfl

/-- The metric is the root distance of `KPApartmentData.rootDistance`. -/
theorem rootDistance_eq_dist (x y : B.Apartment) :
    B.apartment.rootDistance x y = dist x y := by
  rw [root_dist_eq_norm, KPApartmentData.rootDistance, finsum_eq_sum_of_fintype,
    ← RootTranslationMetric.norm_sq B.i (x -ᵥ y), Real.sqrt_sq (norm_nonneg _)]

/-- The Euclidean apartment satisfies the midpoint NPC condition. -/
theorem root_nonpositivelyCurved :
    Langlands.Geometry.Metric.KP.IsNonpositivelyCurved B.Apartment := by
  intro x y
  let e : TranslationSpace B.i ≃ᵢ B.Apartment := IsometryEquiv.vaddConst x
  obtain ⟨m, hm⟩ :=
    Langlands.Geometry.Metric.KP.isNonpositivelyCurved_of_innerProductSpace
      (e.symm x) (e.symm y)
  refine ⟨e m, fun z => ?_⟩
  have h := hm (e.symm z)
  simpa only [← e.dist_eq, e.apply_symm_apply] using h

/-- The Euclidean root metric is proper. -/
theorem root_properSpace : ProperSpace B.Apartment := by
  have := RootTranslationMetric.finiteDimensional B.i
  let e := IsometryEquiv.vaddConst (Classical.arbitrary B.Apartment)
  exact e.isometry.antilipschitzWith.properSpace e.continuous e.surjective

/-- A translate of an apartment point in the image of the apartment differs from it
by a normalizer element (relation (7.6.2)). -/
theorem exists_normalizer_smul_eq_of_smul_apartmentMap_eq {g : rationalPoints G}
    {a b : B.Apartment} (h : g • B.apartmentMap a = B.apartmentMap b) :
    ∃ n : normalizerPoints B.i, n • a = b := by
  have h' : ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, a) =
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := h
  rw [ApartmentQuotient.mk_eq_mk_iff] at h'
  obtain ⟨n, hn, -⟩ := h'
  exact ⟨n, hn⟩

/-- The apartment step of KP Lemma 4.2.11: the normalizer orbits in the apartment are
discrete for the root distance. `N(k)` acts through affine automorphisms permuting the
affine roots, which form a locally finite reflection arrangement. -/
theorem exists_rootDistance_normalizer_smul_lt_imp_eq (b : B.Apartment) :
    ∃ ε > 0, ∀ n : normalizerPoints B.i,
      B.apartment.rootDistance (n • b) b < ε → n • b = b := by
  have := RootTranslationMetric.finiteDimensional B.i
  obtain ⟨ε, hε, h⟩ := AffineRootSystem.exists_forall_dist_lt_imp_eq
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs) b
  refine ⟨ε, hε, fun n hn => ?_⟩
  rw [rootDistance_eq_dist] at hn
  exact h _ (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n) hn

/-! ### Gluing the apartment metrics -/

variable {B}
variable (hcommon : B.apartment.HasCommonApartments)
  {d : B.ReducedBuilding → B.ReducedBuilding → ℝ}
  (hsmul : ∀ (g : rationalPoints G) (x y : B.ReducedBuilding), d (g • x) (g • y) = d x y)
  (hapt : ∀ a b : B.Apartment,
    d (B.apartmentMap a) (B.apartmentMap b) = B.apartment.rootDistance a b)
  (hret : ∀ a : B.Apartment, ∃ ρ : B.ReducedBuilding → B.Apartment,
    (∀ b : B.Apartment, ρ (B.apartmentMap b) = b) ∧
    (∀ x y : B.ReducedBuilding, B.apartment.rootDistance (ρ x) (ρ y) ≤ d x y) ∧
    ∀ x : B.ReducedBuilding, B.apartment.rootDistance a (ρ x) = d (B.apartmentMap a) x)

include hsmul hapt in
theorem smul_apartmentMap_dist (g : rationalPoints G) (a b : B.Apartment) :
    d (g • B.apartmentMap a) (g • B.apartmentMap b) = dist a b := by
  rw [hsmul, hapt, rootDistance_eq_dist]

include hsmul hapt in
theorem injective_smul_apartmentMap (g : rationalPoints G) :
    Function.Injective (fun a : B.Apartment => g • B.apartmentMap a) := by
  intro a b hab
  apply dist_eq_zero.mp
  rw [← smul_apartmentMap_dist hsmul hapt g a b]
  rw [show g • B.apartmentMap b = g • B.apartmentMap a from hab.symm,
    smul_apartmentMap_dist hsmul hapt, dist_self]

include hcommon hsmul hapt hret in
/-- The translated apartments satisfy the gluing hypotheses of KP Propositions 4.2.3(1)
and 4.2.7. -/
theorem isRetractionGluedDistance :
    Metric.KP.IsRetractionGluedDistance d
      {Y | ∃ g : rationalPoints G, Y = g • Set.range B.apartmentMap} where
  exists_common x y := by
    obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
    exact ⟨g • Set.range B.apartmentMap, ⟨g, rfl⟩,
      Set.smul_mem_smul_set (Set.mem_range_self a),
      Set.smul_mem_smul_set (Set.mem_range_self b)⟩
  apartment := by
    rintro _ ⟨g, rfl⟩
    rw [Set.smul_set_range]
    exact Metric.KP.exists_apartmentMetric_of_injective B.root_nonpositivelyCurved d
      (fun a => g • B.apartmentMap a) (injective_smul_apartmentMap hsmul hapt g)
      (smul_apartmentMap_dist hsmul hapt g)
  exists_retraction := by
    rintro _ ⟨g, rfl⟩ m hm
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hm
    obtain ⟨ρ, hρid, hρle, hρa⟩ := hret a
    refine ⟨fun x => g • B.apartmentMap (ρ (g⁻¹ • x)), fun x => ?_, ?_, fun x y => ?_,
      fun x => ?_⟩
    · exact Set.smul_mem_smul_set (Set.mem_range_self _)
    · intro x hx
      obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hx
      simp only [inv_smul_smul, hρid]
    · rw [smul_apartmentMap_dist hsmul hapt, ← rootDistance_eq_dist, ← hsmul g⁻¹ x y]
      exact hρle _ _
    · rw [smul_apartmentMap_dist hsmul hapt, ← rootDistance_eq_dist, hρa, ← hsmul g,
        smul_inv_smul]

/-! ### Completeness -/

section Completeness

variable [MetricSpace B.ReducedBuilding] [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]

theorem dist_smul_apartmentMap (hA : Isometry B.apartmentMap) (h : rationalPoints G)
    (a b : B.Apartment) :
    dist (h • B.apartmentMap a) (h • B.apartmentMap b) = dist a b := by
  rw [dist_smul, hA.dist_eq]

theorem dist_normalizer_smul (hA : Isometry B.apartmentMap) (n : normalizerPoints B.i)
    (a b : B.Apartment) : dist (n • a) (n • b) = dist a b := by
  rw [← hA.dist_eq, ← B.normalizer_smul_apartmentMap, ← B.normalizer_smul_apartmentMap,
    dist_smul, hA.dist_eq]

include hcommon in
/-- KP Lemma 4.2.11 at a point of the base apartment. -/
theorem smul_apartmentMap_eq_of_dist_lt (hA : Isometry B.apartmentMap) {b : B.Apartment}
    {ε : ℝ} (hfix : ∀ n : normalizerPoints B.i, dist (n • b) b < ε → n • b = b)
    (g : rationalPoints G) (hg : dist (g • B.apartmentMap b) (B.apartmentMap b) < ε) :
    g • B.apartmentMap b = B.apartmentMap b := by
  obtain ⟨h, a₁, a₂, ha₁, ha₂⟩ := hcommon (B.apartmentMap b) (g • B.apartmentMap b)
  change h • B.apartmentMap a₁ = _ at ha₁
  change h • B.apartmentMap a₂ = _ at ha₂
  obtain ⟨n₁, hn₁⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq ha₁
  obtain ⟨n₂, hn₂⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq
    (g := g⁻¹ * h) (a := a₂) (b := b) (by rw [mul_smul, ha₂, inv_smul_smul])
  have e₂ : a₂ = n₂⁻¹ • b := by rw [← hn₂, inv_smul_smul]
  have key : dist ((n₁ * n₂⁻¹) • b) b < ε := by
    calc dist ((n₁ * n₂⁻¹) • b) b = dist (n₁ • a₂) (n₁ • a₁) := by
          rw [mul_smul, ← e₂, hn₁]
      _ = dist a₂ a₁ := dist_normalizer_smul hA n₁ a₂ a₁
      _ = dist (g • B.apartmentMap b) (B.apartmentMap b) := by
          rw [← dist_smul_apartmentMap hA h, ha₂, ha₁]
      _ < ε := hg
  have hfixed := hfix _ key
  rw [mul_smul, ← e₂] at hfixed
  have ha : a₂ = a₁ := smul_left_cancel n₁ (hfixed.trans hn₁.symm)
  rw [← ha₂, ha, ha₁]

include hcommon in
/-- KP Lemma 4.2.11: every `G(k)`-orbit in the building is discrete. -/
theorem exists_forall_dist_smul_lt_imp_eq (hA : Isometry B.apartmentMap)
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
  have h := smul_apartmentMap_eq_of_dist_lt hcommon hA hfix _ hg'
  rw [← hconj, h]

include hcommon in
/-- KP Theorem 4.2.10: completeness from isometric apartment charts and discrete
normalizer orbits. -/
theorem completeSpace_of_isometry_apartmentMap (hA : Isometry B.apartmentMap)
    (hdisc : ∀ b : B.Apartment, ∃ ε > 0, ∀ n : normalizerPoints B.i,
      dist (n • b) b < ε → n • b = b) :
    CompleteSpace B.ReducedBuilding := by
  have := B.root_properSpace
  refine Metric.KP.completeSpace_of_discrete_orbits (Γ := rationalPoints G) ?_
    (exists_forall_dist_smul_lt_imp_eq hcommon hA hdisc)
  intro x₀
  obtain ⟨g₀, b, rfl⟩ := B.exists_smul_apartmentMap x₀
  refine ⟨B.apartmentMap '' Metric.closedBall b 1,
    (isCompact_closedBall b 1).image hA.continuous, fun x hx => ?_⟩
  obtain ⟨h, a₀, a, ha₀, ha⟩ := hcommon (g₀ • B.apartmentMap b) x
  change h • B.apartmentMap a₀ = _ at ha₀
  change h • B.apartmentMap a = _ at ha
  obtain ⟨n, hn⟩ := B.exists_normalizer_smul_eq_of_smul_apartmentMap_eq
    (g := g₀⁻¹ * h) (a := a₀) (b := b) (by rw [mul_smul, ha₀, inv_smul_smul])
  refine ⟨h * (n : rationalPoints G)⁻¹, B.apartmentMap (n • a), ⟨n • a, ?_, rfl⟩, ?_⟩
  · rw [Metric.mem_closedBall, ← hn, dist_normalizer_smul hA,
      ← dist_smul_apartmentMap hA h, ha, ha₀]
    exact hx.le
  · rw [← B.normalizer_smul_apartmentMap, mul_smul, inv_smul_smul, ha]

end Completeness

include hcommon hsmul hapt hret in
/-- KP Section 4.2 on the supplied quotient: the glued distance is a complete NPC
metric for which `G(k)` acts isometrically. -/
theorem exists_metric_of_retractionDistance :
    ∃ _ : MetricSpace B.ReducedBuilding,
      (∀ x y : B.ReducedBuilding, dist x y = d x y) ∧
      CompleteSpace B.ReducedBuilding ∧
      Langlands.Geometry.Metric.KP.IsNonpositivelyCurved B.ReducedBuilding ∧
      IsIsometricSMul (rationalPoints G) B.ReducedBuilding := by
  have hglue := isRetractionGluedDistance hcommon hsmul hapt hret
  let := hglue.metricSpace
  have hiso : IsIsometricSMul (rationalPoints G) B.ReducedBuilding :=
    ⟨fun g => Isometry.of_dist_eq (hsmul g)⟩
  have hA : Isometry B.apartmentMap :=
    Isometry.of_dist_eq fun a b => (hapt a b).trans (rootDistance_eq_dist B a b)
  refine ⟨inferInstance, fun _ _ => rfl, ?_, hglue.isNonpositivelyCurved, hiso⟩
  exact completeSpace_of_isometry_apartmentMap hcommon hA fun b => by
    obtain ⟨ε, hε, h⟩ := B.exists_rootDistance_normalizer_smul_lt_imp_eq b
    exact ⟨ε, hε, fun n hn => h n (by rwa [rootDistance_eq_dist])⟩

end IntegerValuationBuildingData

end RootMetric

end Langlands.Geometry.Building
