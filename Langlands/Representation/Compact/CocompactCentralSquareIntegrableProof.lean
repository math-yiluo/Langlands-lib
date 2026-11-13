import Langlands.Representation.Compact.CocompactCentralSquareIntegrableStatements
import Langlands.Representation.Compact.UnitarySquareIntegrableProof
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.L2Space

/-! # Renard IV.3.3, Remark: integrals over `G/A` for a cocompact central subgroup `A` -/

noncomputable section

universe u v

open MeasureTheory Filter Set
open scoped ENNReal NNReal Pointwise

namespace Langlands.Renard.CompactRepresentation

section HaarComparison

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- A set of finite Haar measure that is a union of left cosets of a compact open subgroup is
a finite union of such cosets, hence compact. -/
theorem isCompact_of_mul_right_mem_of_measure_ne_top (m : Measure H) [m.IsHaarMeasure]
    (K : Subgroup H) (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    (S : Set H) (hS : ∀ q ∈ S, ∀ k ∈ K, q * k ∈ S) (hm : m S ≠ ∞) : IsCompact S := by
  classical
  let C : Set (H ⧸ K) := QuotientGroup.mk '' S
  let U : H ⧸ K → Set H := fun c => (fun h => c.out⁻¹ * h) ⁻¹' (K : Set H)
  have hU_meas : ∀ c, MeasurableSet (U c) := fun c =>
    (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hU_mem : ∀ c (h : H), h ∈ U c ↔ (QuotientGroup.mk h : H ⧸ K) = c := by
    intro c h
    change c.out⁻¹ * h ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  have hU_sub : ∀ c ∈ C, U c ⊆ S := by
    rintro c ⟨s, hs, rfl⟩ h hh
    rw [hU_mem, QuotientGroup.eq] at hh
    have := hS s hs _ (K.inv_mem hh)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  have hS_sub : S ⊆ ⋃ c ∈ C, U c := by
    intro s hs
    exact mem_biUnion (mem_image_of_mem _ hs) ((hU_mem _ s).2 rfl)
  have hfin : C.Finite := by
    by_contra hinf
    let e := Set.Infinite.natEmbedding C hinf
    have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => U (e n)) := by
      intro i j hij
      refine Set.disjoint_left.2 fun h hi hj => hij (e.injective (Subtype.ext ?_))
      rw [hU_mem] at hi hj
      exact hi.symm.trans hj
    have hsub : (⋃ n, U (e n)) ⊆ S := iUnion_subset fun n => hU_sub _ (e n).2
    have hK0 : m (K : Set H) ≠ 0 := hKo.measure_ne_zero m ⟨1, K.one_mem⟩
    have htop : m (⋃ n, U (e n)) = ∞ := by
      rw [measure_iUnion hdisj fun n => hU_meas _]
      have hU_eq : ∀ n, m (U (e n)) = m (K : Set H) := fun n =>
        measure_preimage_mul m _ _
      simp_rw [hU_eq]
      exact ENNReal.tsum_const_eq_top_of_ne_zero hK0
    exact hm (top_le_iff.1 (htop ▸ measure_mono hsub))
  have heq : S = ⋃ c ∈ C, U c :=
    Subset.antisymm hS_sub (iUnion₂_subset fun c hc => hU_sub c hc)
  rw [heq]
  exact hfin.isCompact_biUnion fun c _ =>
    (Homeomorph.mulLeft (c.out⁻¹)).isCompact_preimage.2 hKc

variable [LocallyCompactSpace H]

/-- Two Haar measures give proportional lower integrals to a nonnegative measurable function
that is invariant under right translation by a compact open subgroup, provided the lower
integral is finite for the first one. -/
theorem lintegral_ofReal_eq_of_mul_right_invariant (m₁ m₂ : Measure H)
    [m₁.IsHaarMeasure] [m₂.IsHaarMeasure]
    (K : Subgroup H) (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    {f : H → ℝ} (hf : Measurable f) (hnn : ∀ q, 0 ≤ f q)
    (hinv : ∀ q, ∀ k ∈ K, f (q * k) = f q)
    (h : ∫⁻ q, ENNReal.ofReal (f q) ∂m₁ ≠ ∞) :
    ∫⁻ q, ENNReal.ofReal (f q) ∂m₂ =
      (Measure.haarScalarFactor m₂ m₁ : ℝ≥0∞) * ∫⁻ q, ENNReal.ofReal (f q) ∂m₁ := by
  have hS : EqOn (fun t : ℝ => m₂ {q | t < f q})
      (fun t : ℝ => (Measure.haarScalarFactor m₂ m₁ : ℝ≥0∞) * m₁ {q | t < f q}) (Ioi 0) := by
    intro t ht
    have hε : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
    have hfin : m₁ {q | t < f q} ≠ ∞ := by
      have hle : m₁ {q | ENNReal.ofReal t ≤ ENNReal.ofReal (f q)} ≤
          (∫⁻ q, ENNReal.ofReal (f q) ∂m₁) / ENNReal.ofReal t :=
        meas_ge_le_lintegral_div hf.ennreal_ofReal.aemeasurable hε ENNReal.ofReal_ne_top
      refine ne_top_of_le_ne_top (ENNReal.div_lt_top h hε).ne ((measure_mono ?_).trans hle)
      intro q hq
      exact ENNReal.ofReal_le_ofReal (le_of_lt hq)
    have hcpt : IsCompact {q | t < f q} :=
      isCompact_of_mul_right_mem_of_measure_ne_top m₁ K hKo hKc _
        (fun q hq k hk => by
          change t < f (q * k)
          rw [hinv q k hk]
          exact hq) hfin
    change m₂ {q | t < f q} = (Measure.haarScalarFactor m₂ m₁ : ℝ≥0∞) * m₁ {q | t < f q}
    rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure m₂ m₁ hcpt.closure]
    rfl
  rw [lintegral_eq_lintegral_meas_lt m₂ (ae_of_all _ hnn) hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt m₁ (ae_of_all _ hnn) hf.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi hS, lintegral_const_mul' _ _ ENNReal.coe_ne_top]

/-- Integrability of a nonnegative continuous function invariant under right translation by a
compact open subgroup does not depend on the Haar measure. -/
theorem integrable_of_mul_right_invariant (m₁ m₂ : Measure H)
    [m₁.IsHaarMeasure] [m₂.IsHaarMeasure]
    (K : Subgroup H) (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    {f : H → ℝ} (hf : Continuous f) (hnn : ∀ q, 0 ≤ f q)
    (hinv : ∀ q, ∀ k ∈ K, f (q * k) = f q) (h : Integrable f m₁) : Integrable f m₂ := by
  have h₁ := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).1 h.2
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2 ?_⟩
  rw [lintegral_ofReal_eq_of_mul_right_invariant m₁ m₂ K hKo hKc hf.measurable hnn hinv h₁.ne]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h₁

end HaarComparison

section Pushforward

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In a locally compact group, every compact subset of a quotient by a normal subgroup is
covered by the image of a compact subset. -/
theorem exists_isCompact_image_superset [LocallyCompactSpace G] (N : Subgroup G) [N.Normal]
    {C : Set (G ⧸ N)} (hC : IsCompact C) :
    ∃ D : Set G, IsCompact D ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ N) '' D := by
  classical
  choose V hVc hVn using fun g : G => exists_compact_mem_nhds g
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun g : G => (QuotientGroup.mk : G → G ⧸ N) '' interior (V g))
    (fun g => QuotientGroup.isOpenMap_coe _ isOpen_interior) (by
      intro c _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      exact mem_iUnion.2 ⟨g, mem_image_of_mem _ (mem_interior_iff_mem_nhds.2 (hVn g))⟩)
  refine ⟨⋃ g ∈ t, V g, t.isCompact_biUnion fun g _ => hVc g, ht.trans ?_⟩
  refine iUnion₂_subset fun g hg => image_mono (interior_subset.trans ?_)
  exact subset_biUnion_of_mem (u := V) hg

variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)

omit [IsTopologicalGroup G] [A.Normal] in
/-- The image of the centre in `G/A` is compact when `Z(G)/A` is compact. -/
theorem isCompact_image_center
    [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))] :
    IsCompact ((QuotientGroup.mk : G → G ⧸ A) '' (Subgroup.center G : Set G)) := by
  let f : Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G) → G ⧸ A :=
    Quotient.lift (fun z => (QuotientGroup.mk (z : G) : G ⧸ A)) (by
      intro a b hab
      have h := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at h
      exact QuotientGroup.eq.2 (by simpa using h))
  have hf : Continuous f :=
    continuous_quot_lift _ (QuotientGroup.continuous_mk.comp continuous_subtype_val)
  convert isCompact_range hf using 1
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective r
    exact ⟨z, z.2, rfl⟩

/-- The projection `G/A → G/Z(G)` is proper when `Z(G)/A` is compact. -/
theorem tendsto_centralQuotientProjection_cocompact [LocallyCompactSpace G]
    [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))] :
    Tendsto (Langlands.Plancherel.centralQuotientProjection A hA)
      (cocompact (G ⧸ A)) (cocompact (G ⧸ Subgroup.center G)) := by
  refine hasBasis_cocompact.tendsto_right_iff.2 fun C hC => ?_
  obtain ⟨D, hD, hCD⟩ := exists_isCompact_image_superset (Subgroup.center G) hC
  refine mem_cocompact.2 ⟨(QuotientGroup.mk '' D) * (QuotientGroup.mk '' (Subgroup.center G : Set G)),
    (hD.image QuotientGroup.continuous_mk).mul (isCompact_image_center A), ?_⟩
  intro q hq
  by_contra hmem
  apply hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨d, hd, hdg⟩ := hCD (not_not.1 hmem)
  have hz : d⁻¹ * g ∈ Subgroup.center G := QuotientGroup.eq.1 hdg
  refine ⟨QuotientGroup.mk d, mem_image_of_mem _ hd, QuotientGroup.mk (d⁻¹ * g),
    mem_image_of_mem _ hz, ?_⟩
  change ((d * (d⁻¹ * g) : G) : G ⧸ A) = g
  rw [mul_inv_cancel_left]

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

omit [IsTopologicalGroup G] in
theorem measurable_centralQuotientProjection :
    Measurable (Langlands.Plancherel.centralQuotientProjection A hA) :=
  (Langlands.Plancherel.centralQuotientProjection A hA).continuous.measurable

omit [IsTopologicalGroup G] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem surjective_centralQuotientProjection :
    Function.Surjective (Langlands.Plancherel.centralQuotientProjection A hA) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- The pushforward of a Haar measure on `G/A` to `G/Z(G)` is a Haar measure. -/
theorem isHaarMeasure_map_centralQuotientProjection [LocallyCompactSpace G]
    [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))]
    (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] :
    (μ.map (Langlands.Plancherel.centralQuotientProjection A hA)).IsHaarMeasure :=
  Measure.isHaarMeasure_map μ
    (Langlands.Plancherel.centralQuotientProjection A hA).toMonoidHom
    (Langlands.Plancherel.centralQuotientProjection A hA).continuous
    (surjective_centralQuotientProjection A hA)
    (tendsto_centralQuotientProjection_cocompact A hA)

/-- The pushforward of a right-invariant measure on `G/A` to `G/Z(G)` is right invariant. -/
theorem isMulRightInvariant_map_centralQuotientProjection (μ : Measure (G ⧸ A))
    [μ.IsMulRightInvariant] :
    (μ.map (Langlands.Plancherel.centralQuotientProjection A hA)).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  have hp := measurable_centralQuotientProjection A hA
  rw [Measure.map_map (measurable_mul_const _) hp]
  obtain ⟨g, rfl⟩ := surjective_centralQuotientProjection A hA h
  conv_rhs => rw [← map_mul_right_eq_self μ g]
  rw [Measure.map_map hp (measurable_mul_const _)]
  congr 1
  funext y
  simp only [Function.comp_apply, map_mul]

end Pushforward

section Main

open Langlands.HarishChandraSchwartz Langlands.Plancherel

/-- Square integrability of a continuous function invariant under right translation by a
compact open subgroup does not depend on the Haar measure. -/
theorem memLp_two_iff_of_mul_right_invariant {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    (m₁ m₂ : Measure H) [m₁.IsHaarMeasure] [m₂.IsHaarMeasure]
    (K : Subgroup H) (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H))
    {f : H → ℝ} (hf : Continuous f) (hinv : ∀ q, ∀ k ∈ K, f (q * k) = f q) :
    MemLp f 2 m₁ ↔ MemLp f 2 m₂ := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable,
    memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  have hc : Continuous fun q => f q ^ 2 := hf.pow 2
  have hinv' : ∀ q, ∀ k ∈ K, f (q * k) ^ 2 = f q ^ 2 := fun q k hk => by rw [hinv q k hk]
  exact ⟨integrable_of_mul_right_invariant m₁ m₂ K hKo hKc hc (fun q => sq_nonneg _) hinv',
    integrable_of_mul_right_invariant m₂ m₁ K hKo hKc hc (fun q => sq_nonneg _) hinv'⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A smooth representation on which the centre acts through a unitary character carries a
`UnitaryCentralCharacter`: the kernel of the character is open, since it contains the
intersection of the centre with the stabilizer of a nonzero vector (and the trivial character
works on the zero representation). -/
theorem nonempty_unitaryCentralCharacter {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hact : ∀ (z : Subgroup.center G) (v : V), ρ z v = (χ z : ℂ) • v) :
    Nonempty (UnitaryCentralCharacter ρ) := by
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨K, hK⟩ := hρ v
    refine ⟨⟨χ, ?_, hχ, hact⟩⟩
    refine Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap (Subgroup.center G).subtype) ?_
      (K.isOpen.preimage continuous_subtype_val)
    intro z hz
    have h1 : ρ z v = v := hK ⟨z, hz⟩
    rw [hact] at h1
    have h0 : ((χ z : ℂ) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · exact absurd h hv
  · push Not at hV
    refine ⟨⟨1, ?_, fun z => by simp, fun z v => by rw [hV v, map_zero, smul_zero]⟩⟩
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ

/-- The descended coefficient norm of a smooth vector is invariant under right translation by
a compact open subgroup of `G/Z(G)`. -/
theorem exists_compactOpen_coefficientNorm_invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V}
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V) (x : V) (hx : IsSmoothVector ρ x) :
    ∃ K : Subgroup (G ⧸ Subgroup.center G), IsOpen (K : Set (G ⧸ Subgroup.center G)) ∧
      IsCompact (K : Set (G ⧸ Subgroup.center G)) ∧
      ∀ q, ∀ k ∈ K, c.coefficientNorm ℓ x (q * k) = c.coefficientNorm ℓ x q := by
  obtain ⟨K₀, hK₀⟩ := hx
  obtain ⟨L, hLc, hLK⟩ := hcof K₀
  refine ⟨(L : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map, QuotientGroup.coe_mk']
    exact QuotientGroup.isOpenMap_coe _ L.isOpen
  · rw [Subgroup.coe_map, QuotientGroup.coe_mk']
    exact hLc.image QuotientGroup.continuous_mk
  · intro q k hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hl' : ρ l x = x := hK₀ ⟨l, hLK hl⟩
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, c.coefficientNorm_mk,
      c.coefficientNorm_mk]
    change ‖ℓ (ρ (g * l) x)‖ = ‖ℓ (ρ g x)‖
    rw [map_mul, Module.End.mul_apply, hl']

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]

/-- Square integrability of the coefficient norms over `G/A` (with a unitary central
character) gives square integrability of the descended coefficient norms over `G/Z(G)` for the
pushforward measure. -/
theorem exists_memLp_map_of_squareIntegrable (μ : Measure (G ⧸ A))
    (π : SmoothRep.{0, u, v} ℂ G)
    (h : (∃ χ : Subgroup.center G →* ℂˣ, (∀ z, ‖(χ z : ℂ)‖ = 1) ∧
        ∀ (z : Subgroup.center G) (x : π), π.representation (z : G) x = (χ z : ℂ) • x) ∧
      ∀ (ℓ : SmoothDual π.representation) (x : π) (F : G ⧸ A → ℝ),
        (∀ g : G, F (QuotientGroup.mk g) =
          ‖(ℓ : Module.Dual ℂ π) (π.representation g x)‖) →
        MemLp F 2 μ) :
    ∃ c : UnitaryCentralCharacter π.representation,
      ∀ (ℓ : SmoothDual π.representation) (x : π),
        MemLp (c.coefficientNorm ℓ x) 2 (μ.map (centralQuotientProjection A hA)) := by
  obtain ⟨⟨χ, hχ, hact⟩, hL⟩ := h
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter π.isSmooth χ hχ hact
  refine ⟨c, fun ℓ x => ?_⟩
  rw [memLp_map_measure_iff (c.aestronglyMeasurable_coefficientNorm ℓ x (π.isSmooth x) _)
    (measurable_centralQuotientProjection A hA).aemeasurable]
  exact hL ℓ x _ fun g => rfl

omit [IsTopologicalGroup G] in
/-- A function on `G/A` that agrees on representatives with a function on `G/Z(G)` which is
integrable for the pushforward measure is integrable, with the same integral. -/
theorem integrable_integral_of_map (μ : Measure (G ⧸ A)) (Φ : G → ℂ) (F : G ⧸ A → ℂ)
    (F' : G ⧸ Subgroup.center G → ℂ) (hF : ∀ g, F (QuotientGroup.mk g) = Φ g)
    (hF' : ∀ g, F' (QuotientGroup.mk g) = Φ g) {I : ℂ}
    (h : Integrable F' (μ.map (centralQuotientProjection A hA)) ∧
      ∫ q, F' q ∂(μ.map (centralQuotientProjection A hA)) = I) :
    Integrable F μ ∧ ∫ q, F q ∂μ = I := by
  have hp := measurable_centralQuotientProjection A hA
  have he : F = F' ∘ centralQuotientProjection A hA := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hF]
    exact (hF' g).symm
  subst he
  exact ⟨(integrable_map_measure h.1.aestronglyMeasurable hp.aemeasurable).1 h.1,
    (integral_map hp.aemeasurable h.1.aestronglyMeasurable).symm.trans h.2⟩

end Main

/-- Renard IV.3.3, Remark: for a closed subgroup `A ≤ Z(G)` with `Z(G)/A` compact, integrals
over `G/Z(G)` may be replaced by integrals over `G/A`. -/
theorem cocompactCentralSquareIntegrable :
    CocompactCentralSquareIntegrableStatements.{u, v} := by
  intro G _ _ _ _ _ _ A _ _ hA _ _ _ μZ _ _ _ _ μ _ _ ActsBy SqIntModA EssSqIntModA
  let pr := Langlands.Plancherel.centralQuotientProjection A hA
  let ν := μ.map pr
  have : ν.IsHaarMeasure := isHaarMeasure_map_centralQuotientProjection A hA μ
  have : ν.IsMulRightInvariant := isMulRightInvariant_map_centralQuotientProjection A hA μ
  have hp : Measurable pr := measurable_centralQuotientProjection A hA
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- convergence is unaffected
    rintro π ⟨χ, hχ, hact⟩ ℓ x FZ FA hFZ hFA
    obtain ⟨c⟩ := nonempty_unitaryCentralCharacter π.isSmooth χ hχ hact
    have hZ : FZ = c.coefficientNorm ℓ x := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact hFZ g
    have hA' : FA = c.coefficientNorm ℓ x ∘ pr := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact hFA g
    subst hZ hA'
    rw [← memLp_map_measure_iff
      (c.aestronglyMeasurable_coefficientNorm ℓ x (π.isSmooth x) _) hp.aemeasurable]
    obtain ⟨K, hKo, hKc, hinv⟩ :=
      exists_compactOpen_coefficientNorm_invariant hcof c ℓ x (π.isSmooth x)
    exact memLp_two_iff_of_mul_right_invariant μZ ν K hKo hKc
      (c.continuous_coefficientNorm ℓ x (π.isSmooth x)) hinv
  · -- IV.3.2, Proposition
    rintro π hi ⟨ω, hω, hsq⟩
    obtain ⟨c, hc⟩ := exists_memLp_map_of_squareIntegrable A hA μ (π.twist ω hω) hsq
    exact essentiallySquareIntegrableAdmissible G ν π hi ω hω ⟨c, hc⟩
  · -- IV.3.2, Lemma
    intro π hadm hsq
    obtain ⟨c, hc⟩ := exists_memLp_map_of_squareIntegrable A hA μ π hsq
    exact squareIntegrableUnitarySemisimple G ν π ⟨hadm, c, hc⟩
  · -- IV.3.3, Lemma (i)
    rintro π hi ⟨ω, hω, hsq⟩
    obtain ⟨c, hc⟩ := exists_memLp_map_of_squareIntegrable A hA μ (π.twist ω hω) hsq
    obtain ⟨d, hd, hdeg⟩ := (schurOrthogonality G ν).1 π hi ⟨ω, hω, c, hc⟩
    refine ⟨d, hd, fun x₁ x₂ ℓ₁ ℓ₂ F hF => ?_⟩
    let ℓ₁t : SmoothDual (π.twist ω hω).representation :=
      (smoothContragredientTwistEquiv ω π.representation hω).symm ℓ₁
    let ℓ₂t : SmoothDual (π.twist ω hω).representation :=
      (smoothContragredientTwistEquiv ω π.representation hω).symm ℓ₂
    let F' := Langlands.HarishChandraSchwartz.orthogonalityIntegrand (Subgroup.center G)
      c.acts c.acts x₁ ℓ₁t.val x₂ ℓ₂t.val
    have hF' : ∀ g : G, F' (QuotientGroup.mk g) =
        (ℓ₁ : Module.Dual ℂ π) (π.representation g x₁) *
          (ℓ₂ : Module.Dual ℂ π) (π.representation g⁻¹ x₂) := by
      intro g
      change ℓ₁.val ((ω g : ℂ) • π.representation g x₁) *
          ℓ₂.val ((ω g⁻¹ : ℂ) • π.representation g⁻¹ x₂) =
        ℓ₁.val (π.representation g x₁) * ℓ₂.val (π.representation g⁻¹ x₂)
      simp only [map_smul, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val]
      rw [mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    exact integrable_integral_of_map A hA μ _ F F' hF hF' (hdeg x₁ x₂ ℓ₁ ℓ₂ F' hF')
  · -- IV.3.3, Lemma (ii)
    rintro π₁ π₂ hi₁ hi₂ ⟨ω₁, hω₁, hsq₁⟩ ⟨ω₂, hω₂, hsq₂⟩ hne ⟨χ, h₁, h₂⟩
    obtain ⟨c₁, hc₁⟩ := exists_memLp_map_of_squareIntegrable A hA μ (π₁.twist ω₁ hω₁) hsq₁
    obtain ⟨c₂, hc₂⟩ := exists_memLp_map_of_squareIntegrable A hA μ (π₂.twist ω₂ hω₂) hsq₂
    have horth := (schurOrthogonality G ν).2 π₁ π₂ hi₁ hi₂ ⟨ω₁, hω₁, c₁, hc₁⟩
      ⟨ω₂, hω₂, c₂, hc₂⟩ hne ⟨χ, fun z y₁ y₂ => ⟨h₁ z y₁, h₂ z y₂⟩⟩
    intro x₁ x₂ ℓ₁ ℓ₂ F hF
    let F' := Langlands.HarishChandraSchwartz.orthogonalityIntegrand (Subgroup.center G)
      h₁ h₂ x₁ ℓ₁.val x₂ ℓ₂.val
    have hF' : ∀ g : G, F' (QuotientGroup.mk g) =
        (ℓ₁ : Module.Dual ℂ π₁) (π₁.representation g x₁) *
          (ℓ₂ : Module.Dual ℂ π₂) (π₂.representation g⁻¹ x₂) := fun g => rfl
    exact integrable_integral_of_map A hA μ _ F F' hF hF' (horth x₁ x₂ ℓ₁ ℓ₂ F' hF')
  · -- IV.3.3, Corollary
    intro r π hi _ hne _ x ℓ hx hℓ
    exact coefficients_linearIndependent_of_irreducible π hi hne x (fun i => (ℓ i).val) hx
      (fun i h => hℓ i (Subtype.ext h))

end Langlands.Renard.CompactRepresentation
