import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Compatibility of Haar measures on `G` and on `G / A` along an open subgroup

The Library's `TraceFamilyScalar`, `OrbitPolynomialOperator` and `TemperedTwistIntegrability`
relate a Haar measure `μ` on `G` and a Haar measure `ν` on `G / A` by the hypothesis
`hcompat`: the image of `μ` restricted to an open subgroup `N` (there `N = ker p`, standing for
Waldspurger's `G¹`) is `m` times `ν` restricted to the image of `N`. This module proves that such
an `m` exists, is nonzero and finite, when `G` is locally compact and second countable and
`A ∩ N` is compact (as `A_G ∩ G¹` is compact in Waldspurger's setting): the two measures are
left invariant measures on the open subgroup `N A / A` of `G / A`, so Haar uniqueness applies. -/

noncomputable section

open MeasureTheory Measure

open scoped ENNReal Pointwise

namespace Langlands.HarishChandraSchwartz

section Compatibility

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  (A : Subgroup G) [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (ν : Measure (G ⧸ A)) (N : Subgroup G)

/-- The compatibility of `μ` and `ν` along `N` with constant `m`: the image in `G / A` of `μ`
restricted to `N` is `m` times `ν` restricted to the image of `N`. -/
def IsQuotientCompatible (m : ℝ≥0∞) : Prop :=
  Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (N : Set G)) =
    m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (N : Set G))

omit [IsTopologicalGroup G] [A.Normal] in
theorem map_mk_restrict_apply {E : Set (G ⧸ A)} (hE : MeasurableSet E) :
    Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (N : Set G)) E =
      μ ((QuotientGroup.mk : G → G ⧸ A) ⁻¹' E ∩ N) := by
  rw [Measure.map_apply measurable_quotientMk hE,
    Measure.restrict_apply (measurable_quotientMk hE)]

variable [μ.IsMulLeftInvariant]

/-- Translating by the image of an element of `N` preserves the image measure. -/
theorem map_mk_restrict_smul {n : G} (hn : n ∈ N) {E : Set (G ⧸ A)} (hE : MeasurableSet E) :
    Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (N : Set G)) ((n : G ⧸ A) • E) =
      Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (N : Set G)) E := by
  rw [map_mk_restrict_apply μ A N (hE.const_smul _), map_mk_restrict_apply μ A N hE]
  have h1 : (QuotientGroup.mk : G → G ⧸ A) ⁻¹' ((n : G ⧸ A) • E) =
      n • ((QuotientGroup.mk : G → G ⧸ A) ⁻¹' E) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  have h2 : n • (N : Set G) = N := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe]
    exact ⟨fun h => by simpa using N.mul_mem hn h, fun h => N.mul_mem (N.inv_mem hn) h⟩
  rw [h1, ← h2, ← Set.smul_set_inter, h2, measure_smul]

variable [LocallyCompactSpace G] [μ.IsHaarMeasure]

omit [μ.IsMulLeftInvariant] [A.Normal] in
/-- The image measure is finite on compact subsets of the image of `N` when `A ∩ N` is
compact. -/
theorem map_mk_restrict_lt_top (hN : IsOpen (N : Set G))
    (hAN : IsCompact ((A ⊓ N : Subgroup G) : Set G)) {K : Set (G ⧸ A)} (hK : IsCompact K)
    (hKN : K ⊆ (QuotientGroup.mk : G → G ⧸ A) '' N) :
    Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (N : Set G)) K < ⊤ := by
  obtain ⟨V, hVc, hV1, hVN⟩ := exists_compact_subset hN N.one_mem
  -- a finite cover of `K` by images of translates of `interior V`
  have hcover : K ⊆ ⋃ g : N, (QuotientGroup.mk : G → G ⧸ A) '' ((g : G) • interior V) := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hKN hy
    exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, g, Set.mem_smul_set.2 ⟨1, hV1, by simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun g : N => (QuotientGroup.mk : G → G ⧸ A) '' ((g : G) • interior V))
    (fun g => QuotientGroup.isOpenMap_coe _ (isOpen_interior.smul _)) hcover
  set E : Set (G ⧸ A) :=
    ⋃ g ∈ s, (QuotientGroup.mk : G → G ⧸ A) '' ((g : G) • interior V) with hEdef
  have hEo : IsOpen E := isOpen_biUnion fun g _ =>
    QuotientGroup.isOpenMap_coe _ (isOpen_interior.smul _)
  have hsub : (QuotientGroup.mk : G → G ⧸ A) ⁻¹' E ∩ N ⊆
      ⋃ g ∈ s, ((g : G) • V) * ((A ⊓ N : Subgroup G) : Set G) := by
    rintro x ⟨hxE, hxN⟩
    obtain ⟨g, hgs, hgx⟩ := Set.mem_iUnion₂.1 hxE
    obtain ⟨y, hy, hyx⟩ := hgx
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.1 hy
    have hvN : v ∈ N := hVN (interior_subset hv)
    have hyN : (g : G) • v ∈ N := N.mul_mem g.2 hvN
    have ha : ((g : G) • v)⁻¹ * x ∈ A := QuotientGroup.eq.1 hyx
    refine Set.mem_iUnion₂.2 ⟨g, hgs, ?_⟩
    refine ⟨(g : G) • v, Set.smul_mem_smul_set (interior_subset hv), ((g : G) • v)⁻¹ * x,
      ⟨ha, N.mul_mem (N.inv_mem hyN) hxN⟩, by rw [smul_eq_mul]; group⟩
  refine lt_of_le_of_lt (measure_mono hs) ?_
  rw [map_mk_restrict_apply μ A N hEo.measurableSet]
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_)
  refine ENNReal.sum_lt_top.2 fun g _ => ?_
  exact ((hVc.smul (g : G)).mul hAN).measure_lt_top

variable [SecondCountableTopology G] [ν.IsHaarMeasure]

omit [μ.IsMulLeftInvariant] in
/-- **Existence of the compatibility constant**: for `G` locally compact and second countable,
Haar measures `μ` on `G` and `ν` on `G / A`, an open subgroup `N` with `A ∩ N` compact, there is
`m ≠ 0, ∞` with `mk_*(μ|_N) = m ν|_{mk(N)}`. -/
theorem exists_isQuotientCompatible (hN : IsOpen (N : Set G))
    (hAN : IsCompact ((A ⊓ N : Subgroup G) : Set G)) :
    ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ∞ ∧ IsQuotientCompatible μ A ν N m := by
  classical
  set U : Subgroup (G ⧸ A) := N.map (QuotientGroup.mk' A) with hUdef
  have hUcoe : (U : Set (G ⧸ A)) = (QuotientGroup.mk : G → G ⧸ A) '' N := by
    rw [hUdef, Subgroup.coe_map, QuotientGroup.coe_mk']
  have hUo : IsOpen (U : Set (G ⧸ A)) := by
    rw [hUcoe]
    exact QuotientGroup.isOpenMap_coe _ hN
  have hUm : MeasurableSet (U : Set (G ⧸ A)) := hUo.measurableSet
  set lam : Measure (G ⧸ A) := Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict N)
    with hlamdef
  -- `lam` lives on `U`
  have hlamU : lam.restrict U = lam := by
    ext E hE
    rw [Measure.restrict_apply hE, hlamdef, map_mk_restrict_apply μ A N (hE.inter hUm),
      map_mk_restrict_apply μ A N hE]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
    rw [← SetLike.mem_coe, hUcoe]
    exact ⟨x, h.2, rfl⟩
  -- the two measures on the open subgroup `U`
  have : LocallyCompactSpace U := hUo.locallyCompactSpace
  have : SecondCountableTopology U :=
    TopologicalSpace.Subtype.secondCountableTopology (U : Set (G ⧸ A))
  have hemb : Topology.IsOpenEmbedding (U.subtype : U → G ⧸ A) := hUo.isOpenEmbedding_subtypeVal
  have : (ν.comap U.subtype).IsHaarMeasure := IsHaarMeasure.comap ν (mH := inferInstance) hemb
  have hme : MeasurableEmbedding (U.subtype : U → G ⧸ A) := hemb.measurableEmbedding
  have hrange : Set.range (U.subtype : U → G ⧸ A) = U := Subtype.range_coe
  set lamU : Measure U := lam.comap U.subtype with hlamUdef
  have hcomap : ∀ E : Set U, lamU E = lam (Subtype.val '' E) := fun E => by
    rw [hlamUdef, hme.comap_apply]
    rfl
  have : lamU.IsMulLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext E hE
    rw [Measure.map_apply (measurable_const_mul u) hE, hcomap, hcomap]
    obtain ⟨n, hn, hnu⟩ : ∃ n ∈ N, (n : G ⧸ A) = ((u⁻¹ : U) : G ⧸ A) := by
      have := (u⁻¹ : U).2
      rw [← SetLike.mem_coe, hUcoe] at this
      obtain ⟨n, hn, h⟩ := this
      exact ⟨n, hn, h⟩
    have himage : Subtype.val '' ((u * ·) ⁻¹' E) = (n : G ⧸ A) • (Subtype.val '' E) := by
      rw [hnu]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Set.mem_smul_set.2 ⟨((u * x : U) : G ⧸ A), ⟨u * x, hx, rfl⟩, by simp⟩
      · intro hy
        obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hy
        refine ⟨u⁻¹ * x, by simpa using hx, ?_⟩
        simp
    rw [himage, hlamdef]
    exact map_mk_restrict_smul μ A N hn (hme.measurableSet_image' hE)
  have : IsFiniteMeasureOnCompacts lamU := by
    refine ⟨fun K hK => ?_⟩
    rw [hcomap]
    refine map_mk_restrict_lt_top μ A N hN hAN (hK.image continuous_subtype_val) ?_
    rintro _ ⟨x, -, rfl⟩
    rw [← hUcoe]
    exact x.2
  -- Haar uniqueness on `U`
  have huniq := isMulLeftInvariant_eq_smul lamU (ν.comap U.subtype)
  set c := haarScalarFactor lamU (ν.comap U.subtype)
  have hmap : lam = (c : ℝ≥0∞) • ν.restrict U := by
    have h1 : Measure.map U.subtype lamU = lam := by
      rw [hlamUdef, hme.map_comap, hrange, hlamU]
    have h2 : Measure.map U.subtype (ν.comap U.subtype) = ν.restrict U := by
      rw [hme.map_comap, hrange]
    calc lam = Measure.map U.subtype lamU := h1.symm
      _ = Measure.map U.subtype (c • ν.comap U.subtype) := by rw [← huniq]
      _ = c • Measure.map U.subtype (ν.comap U.subtype) := Measure.map_smul _ hme.measurable.aemeasurable
      _ = (c : ℝ≥0∞) • ν.restrict U := by rw [h2]; rfl
  refine ⟨c, ?_, ENNReal.coe_ne_top, ?_⟩
  · intro hc0
    have hpos : 0 < μ (N : Set G) := hN.measure_pos μ ⟨1, N.one_mem⟩
    have h0 : lam Set.univ = 0 := by
      rw [hmap, hc0]
      simp
    rw [hlamdef, map_mk_restrict_apply μ A N MeasurableSet.univ, Set.preimage_univ,
      Set.univ_inter] at h0
    exact hpos.ne' h0
  · change lam = (c : ℝ≥0∞) • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' N)
    rw [hmap, hUcoe]

end Compatibility

end Langlands.HarishChandraSchwartz
