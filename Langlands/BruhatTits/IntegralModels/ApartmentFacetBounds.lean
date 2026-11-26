import Langlands.BruhatTits.IntegralModels.ModelFamily
import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.Geometry.Building.ApartmentConjugacyFixingIntersectionProof

/-! # Facets of an apartment are nonempty, bounded, and lie in the closure of their cofaces;
boundedness does not depend on the apartment chart -/

noncomputable section

universe u uV uA

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A facet is nonempty: it is the class of one of its points. -/
theorem IsFacet.nonempty {F : Set A} (h : IsFacet Ψ F) : F.Nonempty := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, mem_facet_self Ψ x⟩

/-- Each affine root has parallel affine roots on both sides of every point of the
torsor `A`. This is the torsor form of
`IsAffineRootSystemWithRankZero.exists_parallel_roots_opposite_sign`. -/
theorem IsAffineRootSystemWithRankZero.exists_parallel_roots_opposite_sign_of_torsor
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ∃ η ∈ Ψ, ∃ χ ∈ Ψ, η.linear = ψ.linear ∧ χ.linear = ψ.linear ∧
      η p < 0 ∧ 0 < χ p := by
  obtain ⟨η, ⟨hη, hlin⟩, hout⟩ := (hΨ.infinite_fiber ψ hψ).exists_notMem_finite
    (hΨ.finite_bounded_at p (fun _ => 2 * |ψ p| + 1))
  have hlarge : 2 * |ψ p| + 1 < |η p| := by
    by_contra h
    exact hout ⟨hη, le_of_not_gt h⟩
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  let χ : A →ᵃ[ℝ] ℝ := -(η - (2 : ℝ) • ψ)
  have hχ : χ ∈ Ψ := by
    apply hΨ.neg_mem
    have h := hv.2 η hη
    rwa [hlin, hv.1] at h
  have hχlin : χ.linear = ψ.linear := by
    change -(η.linear - (2 : ℝ) • ψ.linear) = ψ.linear
    rw [hlin, two_smul]
    abel
  have hχp : χ p = 2 * ψ p - η p := by
    change -(η p - (2 : ℝ) • ψ p) = _
    simp only [smul_eq_mul]
    ring
  rcases lt_or_gt_of_ne (show η p ≠ 0 by
    intro he
    rw [he, abs_zero] at hlarge
    linarith [abs_nonneg (ψ p)]) with hn | hp
  · refine ⟨η, hη, χ, hχ, hlin, hχlin, hn, ?_⟩
    rw [hχp]
    rw [abs_of_neg hn] at hlarge
    linarith [neg_abs_le (ψ p)]
  · refine ⟨χ, hχ, η, hη, hχlin, hlin, ?_, hp⟩
    rw [hχp]
    rw [abs_of_pos hp] at hlarge
    linarith [le_abs_self (ψ p)]

/-- Every linear form in the span of the derivative roots is bounded on the vectors from `p`
to the points of the closed facet of `p`. -/
theorem IsAffineRootSystemWithRankZero.exists_bound_span_facetClosure
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) {φ : Module.Dual ℝ V}
    (hφ : φ ∈ Submodule.span ℝ (derivativeRoots Ψ)) :
    ∃ M : ℝ, ∀ y ∈ facetClosure Ψ p, |φ (y -ᵥ p)| ≤ M := by
  induction hφ using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨ψ, hψ, hψa⟩ := ha
    change ψ.linear = a at hψa
    obtain ⟨η, hη, χ, hχ, hηlin, hχlin, hηp, hχp⟩ :=
      hΨ.exists_parallel_roots_opposite_sign_of_torsor p hψ
    refine ⟨|η p| + |χ p|, fun y hy => ?_⟩
    have hηy : η y ≤ 0 := by
      rcases hy η hη with h | h
      · exact le_of_eq (sign_eq_zero_iff.mp h)
      · rw [sign_neg hηp, sign_eq_neg_one_iff] at h
        exact le_of_lt h
    have hχy : 0 ≤ χ y := by
      rcases hy χ hχ with h | h
      · exact le_of_eq (sign_eq_zero_iff.mp h).symm
      · rw [sign_pos hχp, sign_eq_one_iff] at h
        exact le_of_lt h
    have hηeq : a (y -ᵥ p) = η y - η p := by
      rw [← hψa, ← hηlin, η.linear_apply_vsub y p, vsub_eq_sub]
    have hχeq : a (y -ᵥ p) = χ y - χ p := by
      rw [← hψa, ← hχlin, χ.linear_apply_vsub y p, vsub_eq_sub]
    exact abs_le.mpr ⟨by linarith [le_abs_self (χ p), abs_nonneg (η p)],
      by linarith [neg_abs_le (η p), abs_nonneg (χ p)]⟩
  | zero => exact ⟨0, fun y _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨M, hM⟩ := ha
    obtain ⟨N, hN⟩ := hb
    refine ⟨M + N, fun y hy => ?_⟩
    rw [LinearMap.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hM y hy) (hN y hy))
  | smul c a _ ha =>
    obtain ⟨M, hM⟩ := ha
    refine ⟨|c| * M, fun y hy => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM y hy) (abs_nonneg c)

/-- Every real affine functional is bounded on every closed facet of an affine root system
(with the rank-zero form of AR 1). -/
theorem IsAffineRootSystemWithRankZero.exists_bound_facetClosure
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) (f : A →ᵃ[ℝ] ℝ) :
    ∃ M : ℝ, ∀ y ∈ facetClosure Ψ p, |f y| ≤ M := by
  obtain ⟨M, hM⟩ := hΨ.exists_bound_span_facetClosure p
    (φ := f.linear) (hΨ.span_derivativeRoots_eq_top ▸ Submodule.mem_top)
  refine ⟨M + |f p|, fun y hy => ?_⟩
  have hfy : f y = f.linear (y -ᵥ p) + f p := by
    rw [f.linear_apply_vsub y p, vsub_eq_sub, sub_add_cancel]
  rw [hfy]
  exact (abs_add_le _ _).trans (add_le_add_left (hM y hy) _)

/-- Every real affine functional is bounded above on every facet. -/
theorem IsAffineRootSystemWithRankZero.bddAbove_image_of_isFacet
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {F : Set A} (hF : IsFacet Ψ F)
    (f : A →ᵃ[ℝ] ℝ) : BddAbove (f '' F) := by
  obtain ⟨p, rfl⟩ := hF
  obtain ⟨M, hM⟩ := hΨ.exists_bound_facetClosure p f
  refine ⟨M, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (le_abs_self _).trans (hM y (facet_subset_facetClosure Ψ p hy))

/-- Suppose the topology on `A` makes every map `g : ℝ → A` continuous whenever every
composite `f ∘ g` with a real affine functional `f` is continuous. Then the closed facet of
`p` lies in the topological closure of the facet of `p`. For each point `q` of the closed
facet, the points `lineMap q p t` for `0 < t ≤ 1` lie in the facet and tend to `q` as
`t → 0⁺`. -/
theorem facetClosure_subset_closure_facet_of_continuous [TopologicalSpace A]
    (hcont : ∀ g : ℝ → A, (∀ f : A →ᵃ[ℝ] ℝ, Continuous (f ∘ g)) → Continuous g)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (p : A) :
    facetClosure Ψ p ⊆ closure (facet Ψ p) := by
  intro q hq
  set c : ℝ → A := fun t => AffineMap.lineMap q p t
  have hc : Continuous c := by
    refine hcont c fun f => ?_
    have : (f ∘ c) = fun t => AffineMap.lineMap (f q) (f p) t := by
      funext t
      simp only [Function.comp_apply, c, AffineMap.apply_lineMap]
    rw [this]
    exact AffineMap.lineMap_continuous
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

end Langlands.Geometry.Building.AffineRootSystem

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (AlgebraicGeometry.Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- A map into the apartment is continuous for the real affine topology as soon as its
composite with every real affine functional is continuous. -/
theorem continuous_of_forall_affineApartmentFunctional {X : Type*} [TopologicalSpace X]
    {g : X → B.Apartment} (hg : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, Continuous (f ∘ g)) :
    @Continuous _ _ _ (affineApartmentTopology B) g := by
  let := affineApartmentTopology B
  exact continuous_iInf_rng.2 fun f => continuous_induced_rng.2 (hg f)

/-- The closed facet of `x` for the affine roots of `B` lies in the ordinary closure (for the
real affine topology) of the facet of `x`. -/
theorem facetClosure_subset_apartmentClosure_facet (x : B.Apartment) :
    facetClosure B.affineRoots x ⊆ apartmentClosure B (facet B.affineRoots x) := by
  let := affineApartmentTopology B
  exact facetClosure_subset_closure_facet_of_continuous
    (fun _ hg => continuous_of_forall_affineApartmentFunctional B hg) B.affineRoots x

/-- A face of a facet lies in the ordinary closure of the facet (KP Remark 1.3.16). No
building axiom is needed. -/
theorem subset_apartmentClosure_of_isFaceOf {Fa Fa' : Set B.Apartment}
    (h : IsFaceOf B.affineRoots Fa Fa') : Fa ⊆ apartmentClosure B Fa' := by
  obtain ⟨-, x, rfl, hsub⟩ := h
  exact hsub.trans (facetClosure_subset_apartmentClosure_facet B x)

/-- A facet of the apartment of `B` for its affine roots is nonempty. -/
theorem nonempty_of_isFacet {Fa : Set B.Apartment} (h : IsFacet B.affineRoots Fa) :
    Fa.Nonempty :=
  h.nonempty

/-- If the affine roots of `B` form an affine root system (rank zero allowed), each facet of
the apartment of `B` is bounded. -/
theorem isBoundedSubset_of_isFacet
    (hΨ : IsAffineRootSystemWithRankZero B.affineRoots) {Fa : Set B.Apartment}
    (h : IsFacet B.affineRoots Fa) : B.IsBoundedSubset Fa :=
  fun f => hΨ.bddAbove_image_of_isFacet h f

/-- Under the apartment axioms of `B` (clause AS 2 for `Ψ`), each facet of the apartment of `B`
is bounded. -/
theorem isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms
    (hB : B.SatisfiesApartmentAxioms) {Fa : Set B.Apartment}
    (h : IsFacet B.affineRoots Fa) : B.IsBoundedSubset Fa :=
  isBoundedSubset_of_isFacet B ((B.satisfiesApartmentAxioms_iff.1 hB).2.2.2.1) h

/-- **Chart independence of boundedness.** Suppose the stabilizer of `A(S)` is `N(F)`, the
apartment chart is injective, and any two apartments `h · A(S)`, `g · A(S)` are conjugate by an
element fixing their intersection pointwise. If a subset of the building is presented as
`g · X` in the chart labelled `g` and as `h · Y` in the chart labelled `h`, with `Y` bounded,
then `X` is bounded: `X` is the image of `Y` under an affine chart transition. -/
theorem isBoundedSubset_of_image_translatedApartmentMap_eq
    (hN : B.HasNormalizerApartmentStabilizer) (hinj : Function.Injective B.apartmentMap)
    (hconj : ∀ g h : rationalPoints G, ∃ k : rationalPoints G,
      k • (h • B.apartmentImage) = g • B.apartmentImage ∧
        ∀ y ∈ (h • B.apartmentImage) ∩ g • B.apartmentImage, k • y = y)
    {g h : rationalPoints G} {X Y : Set B.Apartment}
    (hXY : B.translatedApartmentMap g '' X = B.translatedApartmentMap h '' Y)
    (hY : B.IsBoundedSubset Y) : B.IsBoundedSubset X := by
  obtain ⟨k, hk, hfix⟩ := hconj g h
  have hn : g⁻¹ * (k * h) ∈ normalizerPoints B.i := by
    rw [← B.smul_apartmentImage_eq_iff hN, mul_smul]
    exact hk
  set ν := B.apartmentChartTransition (k * h) g hn
  have hXν : X = ν '' Y := by
    apply (B.translatedApartmentMap_injective hinj g).image_injective
    rw [hXY, ← Set.image_comp]
    refine Set.image_congr fun y hy => ?_
    rw [Function.comp_apply, B.translatedApartmentMap_transition,
      B.translatedApartmentMap_mul]
    symm
    apply hfix
    refine ⟨Set.smul_mem_smul_set (Set.mem_range_self y), ?_⟩
    have hmem : B.translatedApartmentMap h y ∈ B.translatedApartmentMap g '' X :=
      hXY ▸ ⟨y, hy, rfl⟩
    obtain ⟨x, -, hx⟩ := hmem
    rw [← hx]
    exact Set.smul_mem_smul_set (Set.mem_range_self x)
  intro f
  rw [hXν, ← Set.image_comp]
  exact hY (f.comp ν.toAffineMap)

/-- **Chart independence of boundedness under the target axioms.** For supplied parahoric
building data satisfying the seven predicates of the corrected opening of KP Section 4.2
(Axioms 4.1.1 for `G`, 4.1.2, 4.1.4, 4.1.6, 4.1.9), any two apartment presentations
`g · X = h · Y` of the same subset of `B(G)` with `Y` bounded have `X` bounded. The conjugacy
input is the Library's proved KP Proposition 4.2.24 (`apartmentConjugacyFixingIntersection`). -/
theorem isBoundedSubset_of_image_translatedApartmentMap_eq_of_axioms
    (P : ParahoricBuildingData G) (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting)
    (h1 : P.SatisfiesBuildingAxiom R) (h2 : P.HasBoundedOpenStabilizers)
    (h3 : P.SatisfiesAffineApartmentAxiom T) (h4 : P.HasRootReflections)
    (h5 : P.SatisfiesApartmentAxioms) (h6 : P.HasCompatibleApartmentFacets)
    (h7 : P.HasTitsSystem) {g h : rationalPoints G}
    {X Y : Set P.toValuationBuildingData.Apartment}
    (hXY : P.toValuationBuildingData.translatedApartmentMap g '' X =
      P.toValuationBuildingData.translatedApartmentMap h '' Y)
    (hY : P.toValuationBuildingData.IsBoundedSubset Y) :
    P.toValuationBuildingData.IsBoundedSubset X :=
  isBoundedSubset_of_image_translatedApartmentMap_eq P.toValuationBuildingData
    h1.normalizerApartmentStabilizer h6.injective
    (fun g h => by
      obtain ⟨k, -, hk, hfix⟩ := apartmentConjugacyFixingIntersection K G P R T
        h1 h2 h3 h4 h5 h6 h7 (h • P.toValuationBuildingData.apartmentImage)
        (g • P.toValuationBuildingData.apartmentImage) ⟨h, rfl⟩ ⟨g, rfl⟩
      exact ⟨k, hk, hfix⟩)
    hXY hY

end Langlands.BruhatTits.IntegralModels
