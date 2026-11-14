import Langlands.Geometry.Building.IntegerValuationBuildingMetricReduction
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.GenericApartmentPairNormalizer
import Langlands.Geometry.Building.FacetClosureLipschitz
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # Retraction distance on an integer-valued building

KP Proposition 1.5.24, Definition 1.5.25 and Lemma 4.2.2 for the supplied
integer-valued quotient. The distance is the root distance read in a common
translated apartment; the retraction onto the base apartment is the chamber
retraction `ρ_{A,C}` built from the sharp fixer of a chamber `C` whose closure
contains the chosen point.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

open AffineRootSystem AffineRootSystem.GalleryGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

attribute [local instance] rootDistanceFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : InnerProductSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.innerProductSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

attribute [local instance] rootMetricSpace rootNormedAddTorsor

/-! ### The chart distance -/

/-- Common-apartment coverage, stated with the apartment map of `B`. -/
theorem exists_smul_apartmentMap_pair (hcommon : B.apartment.HasCommonApartments)
    (x y : B.ReducedBuilding) :
    ∃ (g : rationalPoints G) (a b : B.Apartment),
      g • B.apartmentMap a = x ∧ g • B.apartmentMap b = y :=
  hcommon x y

/-- The root distance of chosen coordinates of `x` and `y` in one translated
apartment; it does not depend on the choice (`retractionDistance_smul_apartmentMap`). -/
def retractionDistance (hcommon : B.apartment.HasCommonApartments)
    (x y : B.ReducedBuilding) : ℝ :=
  B.apartment.rootDistance (B.exists_smul_apartmentMap_pair hcommon x y).choose_spec.choose
    (B.exists_smul_apartmentMap_pair hcommon x y).choose_spec.choose_spec.choose

/-- In every translated apartment the distance is the Euclidean root distance. -/
theorem retractionDistance_smul_apartmentMap (hcommon : B.apartment.HasCommonApartments)
    (g : rationalPoints G) (a b : B.Apartment) :
    B.retractionDistance hcommon (g • B.apartmentMap a) (g • B.apartmentMap b) =
      dist a b := by
  have h := B.exists_smul_apartmentMap_pair hcommon (g • B.apartmentMap a)
    (g • B.apartmentMap b)
  obtain ⟨ha, hb⟩ := h.choose_spec.choose_spec.choose_spec
  rw [retractionDistance, rootDistance_eq_dist, root_dist_eq_norm, root_dist_eq_norm]
  refine (B.apartment.norm_vsub_eq_of_two_apartmentMap_eq B.isConnectedReductive
    B.isMaximalSplitTorus (g⁻¹ * h.choose) _ _ a b ?_ ?_).symm
  · rw [mul_smul, ha, inv_smul_smul]
  · rw [mul_smul, hb, inv_smul_smul]

/-- The distance is invariant under the rational points. -/
theorem retractionDistance_smul (hcommon : B.apartment.HasCommonApartments)
    (h : rationalPoints G) (x y : B.ReducedBuilding) :
    B.retractionDistance hcommon (h • x) (h • y) = B.retractionDistance hcommon x y := by
  obtain ⟨g, a, b, rfl, rfl⟩ := B.exists_smul_apartmentMap_pair hcommon x y
  rw [← mul_smul, ← mul_smul, retractionDistance_smul_apartmentMap,
    retractionDistance_smul_apartmentMap]

/-! ### Sharp fixers of chambers -/

/-- The sharp fixer of the facet of `c` fixes every point of its closure. -/
theorem smul_apartmentMap_eq_of_mem_sharpFixer_facet {c y : B.Apartment}
    (hy : y ∈ facetClosure B.affineRoots c) {p : rationalPoints G}
    (hp : p ∈ B.apartment.sharpFixer (facet B.affineRoots c)) :
    p • B.apartmentMap y = B.apartmentMap y :=
  B.apartment.mem_reducedFixer.mp (B.apartment.sharpFixer_le_reducedFixer y
    (B.sharpFixer_facet_le_singleton_of_mem_facetClosure hy hp))

/-- KP Proposition 1.5.24 for two chambers: every rational point is a product
`p n q` with `p` in the sharp fixer of the facet of `c`, `n` in the normalizer and
`q` in the sharp fixer of the facet of `d`, for regular points `c` and `d`. -/
theorem exists_sharpFixer_facet_normalizer_mul
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c d : B.Apartment} (hc : IsRegular B.affineRoots c) (hd : IsRegular B.affineRoots d)
    (g : rationalPoints G) :
    ∃ p ∈ B.apartment.sharpFixer (facet B.affineRoots c), ∃ n : normalizerPoints B.i,
      ∃ q ∈ B.apartment.sharpFixer (facet B.affineRoots d),
        g = p * (n : rationalPoints G) * q := by
  have hsys := B.isAffineRootSystemWithRankZero_affineRoots hunit
  have hC : AffineRootSystem.IsChamber B.affineRoots (facet B.affineRoots c) := ⟨c, hc, rfl⟩
  have hD : AffineRootSystem.IsChamber B.affineRoots (facet B.affineRoots d) := ⟨d, hd, rfl⟩
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _ hsys _ _ hC hD
  obtain ⟨m, hm⟩ := B.affineWeylGroup_le_range w.property
  have hmC : m • facet B.affineRoots c = facet B.affineRoots d := by
    change (B.apartment.normalizerAffineEquiv m : B.Apartment → B.Apartment) '' _ = _
    rw [hm]
    exact hw
  obtain ⟨p, hp, n, q, hq, hg⟩ :=
    B.mem_sharpChamberNormalizerCover hunit hC (g * (m : rationalPoints G))
  have hq' := B.apartment.sharpFixer_le_comap m (facet B.affineRoots c) hq
  change (m : rationalPoints G) * q * (m : rationalPoints G)⁻¹ ∈
    B.apartment.sharpFixer (m • facet B.affineRoots c) at hq'
  rw [hmC] at hq'
  refine ⟨p, hp, n * m⁻¹, (m : rationalPoints G) * q * (m : rationalPoints G)⁻¹, hq', ?_⟩
  have hg' := congrArg (fun z : rationalPoints G => z * (m : rationalPoints G)⁻¹) hg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc
    g = (p * (n : rationalPoints G) * q) * (m : rationalPoints G)⁻¹ := by
      simpa only [mul_inv_cancel_right] using hg'
    _ = _ := by group

/-- Two apartment points with equal root distances to every point of an open
chamber coincide. -/
theorem eq_of_forall_mem_facet_norm_vsub_eq {c : B.Apartment} (hc : IsRegular B.affineRoots c)
    {b b' : B.Apartment}
    (h : ∀ z ∈ facet B.affineRoots c,
      ‖(z -ᵥ b' : TranslationSpace B.i)‖ = ‖(z -ᵥ b : TranslationSpace B.i)‖) :
    b = b' := by
  have hloc := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  set w : TranslationSpace B.i := b' -ᵥ b with hw
  set u : TranslationSpace B.i := c -ᵥ b' with hu
  obtain ⟨ε, hε, hs⟩ := exists_pos_of_eventually (eventually_sign_smul_vadd hloc c w)
  have hmem : ε • w +ᵥ c ∈ facet B.affineRoots c := fun ψ hψ => (hs ψ hψ (hc ψ hψ)).symm
  have hcb : (c -ᵥ b : TranslationSpace B.i) = u + w := by
    rw [hu, hw, vsub_add_vsub_cancel]
  have h0 := h c (mem_facet_self _ c)
  have h1 := h _ hmem
  rw [vadd_vsub_assoc, vadd_vsub_assoc, hcb] at h1
  rw [hcb] at h0
  rw [← hu] at h0 h1
  have e0 := congrArg (· ^ 2) h0
  have e1 := congrArg (· ^ 2) h1
  rw [← add_assoc, norm_add_sq_real (ε • w + u) w, norm_add_sq_real (ε • w) u,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at e1
  rw [norm_add_sq_real u w] at e0
  have hww : ε * ‖w‖ ^ 2 = 0 := by
    have hcomm : inner ℝ u w = inner ℝ w u := real_inner_comm _ _
    nlinarith
  have hw0 : ‖w‖ = 0 := by
    rcases mul_eq_zero.mp hww with h' | h'
    · exact absurd h' hε.ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  have : w = 0 := norm_eq_zero.mp hw0
  rw [hw, vsub_eq_zero_iff_eq] at this
  exact this.symm

/-- Uniqueness in KP Proposition 1.5.24: an element of the sharp fixer of an open
chamber carrying an apartment point into the apartment fixes it. -/
theorem eq_of_mem_sharpFixer_facet_smul_apartmentMap_eq {c : B.Apartment}
    (hc : IsRegular B.affineRoots c) {p : rationalPoints G}
    (hp : p ∈ B.apartment.sharpFixer (facet B.affineRoots c)) {b b' : B.Apartment}
    (h : p • B.apartmentMap b = B.apartmentMap b') : b = b' :=
  B.eq_of_forall_mem_facet_norm_vsub_eq hc fun z hz =>
    B.apartment.norm_vsub_eq_of_two_apartmentMap_eq B.isConnectedReductive
      B.isMaximalSplitTorus p z b z b'
      (B.smul_apartmentMap_eq_of_mem_sharpFixer_facet
        (facet_subset_facetClosure _ _ hz) hp) h

/-- Existence in KP Proposition 1.5.24: every point of the building is carried
into the apartment by the sharp fixer of an open chamber. -/
theorem exists_sharpFixer_facet_smul_apartmentMap_eq
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) (x : B.ReducedBuilding) :
    ∃ b : B.Apartment, ∃ p ∈ B.apartment.sharpFixer (facet B.affineRoots c),
      p • B.apartmentMap b = x := by
  have hloc := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  obtain ⟨g, a, rfl⟩ := B.exists_smul_apartmentMap x
  obtain ⟨d, hd, had⟩ := hloc.exists_regularPoint_closure a
  obtain ⟨p, hp, n, q, hq, rfl⟩ := B.exists_sharpFixer_facet_normalizer_mul hunit hc hd g
  refine ⟨n • a, p, hp, ?_⟩
  rw [mul_smul, mul_smul, B.smul_apartmentMap_eq_of_mem_sharpFixer_facet had hq,
    B.normalizer_smul_apartmentMap]

/-- The chamber retraction `ρ_{A,C}` onto the apartment, for the chamber `C` of a
regular point `c` (KP Definition 1.5.25). -/
def chamberRetraction (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) (x : B.ReducedBuilding) :
    B.Apartment :=
  (B.exists_sharpFixer_facet_smul_apartmentMap_eq hunit hc x).choose

theorem exists_smul_apartmentMap_chamberRetraction
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) (x : B.ReducedBuilding) :
    ∃ p ∈ B.apartment.sharpFixer (facet B.affineRoots c),
      p • B.apartmentMap (B.chamberRetraction hunit hc x) = x :=
  (B.exists_sharpFixer_facet_smul_apartmentMap_eq hunit hc x).choose_spec

/-- Any element of the sharp fixer of the chamber carrying `x` into the apartment
computes the retraction. -/
theorem chamberRetraction_eq (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) {p : rationalPoints G}
    (hp : p ∈ B.apartment.sharpFixer (facet B.affineRoots c)) {b : B.Apartment}
    {x : B.ReducedBuilding} (hx : p • B.apartmentMap b = x) :
    B.chamberRetraction hunit hc x = b := by
  obtain ⟨p', hp', hx'⟩ := B.exists_smul_apartmentMap_chamberRetraction hunit hc x
  refine B.eq_of_mem_sharpFixer_facet_smul_apartmentMap_eq hc
    (mul_mem (inv_mem hp) hp') ?_
  rw [mul_smul, hx', ← hx, inv_smul_smul]

/-- The chamber retraction fixes the apartment. -/
theorem chamberRetraction_apartmentMap (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) (b : B.Apartment) :
    B.chamberRetraction hunit hc (B.apartmentMap b) = b :=
  B.chamberRetraction_eq hunit hc (one_mem _) (one_smul _ _)

/-- On a translated apartment the retraction is the action of a normalizer element
near every closed facet. -/
theorem dist_chamberRetraction_le_of_mem_facetClosure
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {c : B.Apartment} (hc : IsRegular B.affineRoots c) (g : rationalPoints G)
    {p₀ x y : B.Apartment} (hx : x ∈ facetClosure B.affineRoots p₀)
    (hy : y ∈ facetClosure B.affineRoots p₀) :
    dist (B.chamberRetraction hunit hc (g • B.apartmentMap x))
      (B.chamberRetraction hunit hc (g • B.apartmentMap y)) ≤ dist x y := by
  have hloc := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  obtain ⟨d, hd, hpd⟩ := hloc.exists_regularPoint_closure p₀
  obtain ⟨p, hp, n, q, hq, rfl⟩ := B.exists_sharpFixer_facet_normalizer_mul hunit hc hd g
  have hret : ∀ z ∈ facetClosure B.affineRoots p₀,
      B.chamberRetraction hunit hc ((p * (n : rationalPoints G) * q) • B.apartmentMap z) =
        n • z := by
    intro z hz
    refine B.chamberRetraction_eq hunit hc hp ?_
    rw [mul_smul, mul_smul, B.smul_apartmentMap_eq_of_mem_sharpFixer_facet
      (mem_facetClosure_trans hpd hz) hq, B.normalizer_smul_apartmentMap]
  rw [hret x hx, hret y hy, root_dist_eq_norm, root_dist_eq_norm]
  exact (B.apartment.norm_vsub_eq_of_two_apartmentMap_eq B.isConnectedReductive
    B.isMaximalSplitTorus n x y (n • x) (n • y)
    (B.normalizer_smul_apartmentMap n x) (B.normalizer_smul_apartmentMap n y)).le

/-- KP Proposition 4.2.1 and Lemma 4.2.2 for the supplied integer-valued quotient
with an order-one unit. -/
theorem exists_retractionDistance (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) :
    ∃ d : B.ReducedBuilding → B.ReducedBuilding → ℝ,
      (∀ (g : rationalPoints G) (x y : B.ReducedBuilding), d (g • x) (g • y) = d x y) ∧
      (∀ a b : B.Apartment,
        d (B.apartmentMap a) (B.apartmentMap b) = B.apartment.rootDistance a b) ∧
      ∀ a : B.Apartment, ∃ ρ : B.ReducedBuilding → B.Apartment,
        (∀ b : B.Apartment, ρ (B.apartmentMap b) = b) ∧
        (∀ x y : B.ReducedBuilding, B.apartment.rootDistance (ρ x) (ρ y) ≤ d x y) ∧
        ∀ x : B.ReducedBuilding, B.apartment.rootDistance a (ρ x) = d (B.apartmentMap a) x := by
  have hcommon := B.hasCommonApartments hunit
  have hloc := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  refine ⟨B.retractionDistance hcommon, B.retractionDistance_smul hcommon,
    fun a b => ?_, fun a => ?_⟩
  · rw [rootDistance_eq_dist, ← B.retractionDistance_smul_apartmentMap hcommon 1, one_smul,
      one_smul]
  obtain ⟨c, hc, hac⟩ := hloc.exists_regularPoint_closure a
  refine ⟨B.chamberRetraction hunit hc, B.chamberRetraction_apartmentMap hunit hc,
    fun x y => ?_, fun x => ?_⟩
  · obtain ⟨g, u, w, rfl, rfl⟩ := B.exists_smul_apartmentMap_pair hcommon x y
    rw [rootDistance_eq_dist, B.retractionDistance_smul_apartmentMap]
    exact AffineRootSystem.dist_le_of_forall_mem_facetClosure (Ψ := B.affineRoots)
      hloc.finite_bounded_at
      (f := fun z => B.chamberRetraction hunit hc (g • B.apartmentMap z))
      (fun p₀ x y hx hy => B.dist_chamberRetraction_le_of_mem_facetClosure hunit hc g hx hy)
      u w
  · obtain ⟨p, hp, hx⟩ := B.exists_smul_apartmentMap_chamberRetraction hunit hc x
    conv_rhs => rw [← hx, ← B.smul_apartmentMap_eq_of_mem_sharpFixer_facet hac hp]
    rw [B.retractionDistance_smul_apartmentMap, rootDistance_eq_dist]

end IntegerValuationBuildingData

end Langlands.Geometry.Building
