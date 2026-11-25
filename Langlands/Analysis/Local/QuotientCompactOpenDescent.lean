import Langlands.Analysis.Local.QuotientNormalizingFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure

/-!
# Integrals over a quotient through a compact open subgroup

Let `j : H →* G` be a closed embedding of locally compact, second countable groups with left Haar
measures `μG`, `μH`, `K` a compact open subgroup of `G`, `T` a closed subgroup of `H` and
`S = j(T)`, with right-invariant measures `μS`, `μT` that correspond under `j`, and quotient measures
`νS`, `νT` compatible with `(μG, μS)` and `(μH, μT)`. For a measurable left `S`-invariant function
`Φ` on `G` supported in `j(H) K` whose descent to `S \ G` is `νS`-integrable,

`∫_{S\G} Φ dνS = μH(K ∩ H)⁻¹ ∫_{T\H} (h ↦ ∫_K Φ(j(h) κ) dμG(κ)) dνT`

(`IsCompatible.integral_descend_eq_of_compactOpen`). This is the passage from integrals over `K`
to orbital integrals in the matching of test functions near the identity. See the paired Markdown.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal NNReal Pointwise

section CompactOpen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H]

/-- The density `g ↦ ∫⁻ h, ρ h · 1_K (j(h)⁻¹ g) dμH` on `G`. -/
private def compactOpenDensity (j : H →* G) (μH : Measure H) (ρ : H → ℝ≥0) (K : Subgroup G)
    (g : G) : ℝ≥0∞ :=
  ∫⁻ h, (ρ h : ℝ≥0∞) * (K : Set G).indicator 1 ((j h)⁻¹ * g) ∂μH

variable [SecondCountableTopology G] [SecondCountableTopology H]

omit [IsTopologicalGroup H] [SecondCountableTopology H] in
private theorem measurable_compactOpenDensity {j : H →* G} (hj : Continuous j) (μH : Measure H)
    [SFinite μH] {ρ : H → ℝ≥0} (hρ : Measurable ρ) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) : Measurable (compactOpenDensity j μH ρ K) := by
  have hf : Measurable fun p : H × G => (ρ p.1 : ℝ≥0∞) * (K : Set G).indicator 1 ((j p.1)⁻¹ * p.2) :=
    (hρ.coe_nnreal_ennreal.comp measurable_fst).mul
      ((measurable_one.indicator hK).comp
        (((hj.comp continuous_fst).inv.mul continuous_snd).measurable))
  exact hf.lintegral_prod_left'

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H] [SecondCountableTopology G]
  [SecondCountableTopology H] in
private theorem compactOpenDensity_eq_zero {j : H →* G} {μH : Measure H} {ρ : H → ℝ≥0}
    {K : Subgroup G} {g : G} (hg : ∀ h : H, (j h)⁻¹ * g ∉ K) :
    compactOpenDensity j μH ρ K g = 0 := by
  refine (lintegral_congr fun h => ?_).trans lintegral_zero
  simp [indicator_of_notMem (hg h)]

/-- `μG.withDensity b` is the image of `(μH.withDensity ρ) ⊗ μG|_K` under `(h, κ) ↦ j h κ`. -/
private theorem withDensity_compactOpenDensity {j : H →* G} (hj : Continuous j)
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG] (μH : Measure H) [SFinite μH]
    {ρ : H → ℝ≥0} (hρ : Measurable ρ) {K : Subgroup G} (hK : MeasurableSet (K : Set G)) :
    μG.withDensity (compactOpenDensity j μH ρ K) =
      ((μH.withDensity fun h => (ρ h : ℝ≥0∞)).prod (μG.restrict K)).map
        (fun p : H × G => j p.1 * p.2) := by
  have hm : Measurable fun p : H × G => j p.1 * p.2 :=
    ((hj.comp continuous_fst).mul continuous_snd).measurable
  have hb := measurable_compactOpenDensity hj μH hρ hK
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hjm : Measurable j := hj.measurable
  have hg2 : Measurable fun h : H => ∫⁻ κ in (K : Set G), f (j h * κ) ∂μG :=
    (hf.comp hm).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hb hf, lintegral_map hf hm,
    lintegral_prod (fun p : H × G => f (j p.1 * p.2)) (hf.comp hm).aemeasurable]
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ.coe_nnreal_ennreal hg2]
  have hF : Measurable fun p : H × G =>
      (ρ p.1 : ℝ≥0∞) * (K : Set G).indicator 1 ((j p.1)⁻¹ * p.2) * f p.2 :=
    ((hρ.coe_nnreal_ennreal.comp measurable_fst).mul
      ((measurable_one.indicator hK).comp
        (((hj.comp continuous_fst).inv.mul continuous_snd).measurable))).mul
      (hf.comp measurable_snd)
  calc ∫⁻ g, (compactOpenDensity j μH ρ K * f) g ∂μG
      = ∫⁻ g, ∫⁻ h, (ρ h : ℝ≥0∞) * (K : Set G).indicator 1 ((j h)⁻¹ * g) * f g ∂μH ∂μG := by
        refine lintegral_congr fun g => ?_
        simp only [Pi.mul_apply, compactOpenDensity]
        exact (lintegral_mul_const _ (hρ.coe_nnreal_ennreal.mul
          ((measurable_one.indicator hK).comp (hjm.inv.mul_const g)))).symm
    _ = ∫⁻ h, ∫⁻ g, (ρ h : ℝ≥0∞) * (K : Set G).indicator 1 ((j h)⁻¹ * g) * f g ∂μG ∂μH :=
        lintegral_lintegral_swap (hF.comp measurable_swap).aemeasurable
    _ = ∫⁻ h, (ρ h : ℝ≥0∞) * ∫⁻ κ, f (j h * κ) ∂μG.restrict K ∂μH := by
        refine lintegral_congr fun h => ?_
        simp_rw [mul_assoc]
        have hmeas : Measurable fun g : G =>
            (K : Set G).indicator (1 : G → ℝ≥0∞) ((j h)⁻¹ * g) * f g :=
          ((measurable_one.indicator hK).comp (measurable_const_mul _)).mul hf
        rw [lintegral_const_mul _ hmeas]
        congr 1
        rw [← lintegral_mul_left_eq_self _ (j h), ← lintegral_indicator hK]
        refine lintegral_congr fun κ => ?_
        by_cases hκ : κ ∈ (K : Set G)
        · simp [indicator_of_mem hκ]
        · simp [indicator_of_notMem hκ]
    _ = ∫⁻ h, ((fun h => (ρ h : ℝ≥0∞)) * fun h => ∫⁻ κ, f (j h * κ) ∂μG.restrict K) h ∂μH := rfl



omit [IsTopologicalGroup G] [SecondCountableTopology G] in
/-- The fibre integral of the density: for `g = j h₀ κ₀` with `κ₀ ∈ K` and `ρ` a normalizing
function of `T`, `∫⁻ t, b (j t g) dμT = μH (K.comap j)`. -/
private theorem lintegral_compactOpenDensity_eq {j : H →* G} (hj : Continuous j)
    (μH : Measure H) [μH.IsMulLeftInvariant] [SFinite μH]
    {T : Subgroup H} [MeasurableSpace T] [BorelSpace T] (μT : Measure T) [SFinite μT]
    {ρ : H → ℝ≥0} (hρm : Measurable ρ)
    (hρ : IsNormalizingFunction T μT fun h => (ρ h : ℝ≥0∞))
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (h₀ : H) {κ₀ : G} (hκ₀ : κ₀ ∈ K) :
    ∫⁻ t : T, compactOpenDensity j μH ρ K (j t * (j h₀ * κ₀)) ∂μT = μH (K.comap j) := by
  have hKH : MeasurableSet ((K.comap j : Subgroup H) : Set H) := hK.preimage hj.measurable
  have e1 : ∀ t : T, compactOpenDensity j μH ρ K (j t * (j h₀ * κ₀)) =
      ∫⁻ h', (ρ (t.val * (h₀ * h')) : ℝ≥0∞) *
        ((K.comap j : Subgroup H) : Set H).indicator 1 h' ∂μH := by
    intro t
    unfold compactOpenDensity
    rw [← lintegral_mul_left_eq_self _ (t.val * h₀)]
    refine lintegral_congr fun h' => ?_
    have e2 : (j (t.val * h₀ * h'))⁻¹ * (j t * (j h₀ * κ₀)) = (j h')⁻¹ * κ₀ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [e2, mul_assoc]
    congr 1
    by_cases hh : h' ∈ K.comap j
    · have hm : (j h')⁻¹ * κ₀ ∈ K := K.mul_mem (K.inv_mem hh) hκ₀
      rw [indicator_of_mem (show (j h')⁻¹ * κ₀ ∈ (K : Set G) from hm),
        indicator_of_mem (show h' ∈ ((K.comap j : Subgroup H) : Set H) from hh)]
      rfl
    · have hm : (j h')⁻¹ * κ₀ ∉ K := fun hm =>
        hh (K.inv_mem_iff.mp ((K.mul_mem_cancel_right hκ₀).mp hm))
      rw [indicator_of_notMem (show (j h')⁻¹ * κ₀ ∉ (K : Set G) from hm),
        indicator_of_notMem (show h' ∉ ((K.comap j : Subgroup H) : Set H) from hh)]
  simp_rw [e1]
  have hF : Measurable fun p : T × H => (ρ (p.1.val * (h₀ * p.2)) : ℝ≥0∞) *
      ((K.comap j : Subgroup H) : Set H).indicator 1 p.2 :=
    (hρm.coe_nnreal_ennreal.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.mul continuous_snd)).measurable).mul
      ((measurable_one.indicator hKH).comp measurable_snd)
  rw [lintegral_lintegral_swap hF.aemeasurable]
  have e3 : ∀ h' : H, ∫⁻ t : T, (ρ (t.val * (h₀ * h')) : ℝ≥0∞) *
      ((K.comap j : Subgroup H) : Set H).indicator 1 h' ∂μT =
        ((K.comap j : Subgroup H) : Set H).indicator 1 h' := by
    intro h'
    have hm : Measurable fun t : T => (ρ (t.val * (h₀ * h')) : ℝ≥0∞) :=
      hρ.measurable.comp (continuous_subtype_val.mul_const (h₀ * h')).measurable
    rw [lintegral_mul_const _ hm, hρ.lintegral_eq_one, one_mul]
  simp_rw [e3]
  rw [lintegral_indicator_one hKH]



variable [T2Space G] [LocallyCompactSpace G] [T2Space H] [LocallyCompactSpace H]

/-- **Integrals over `S \ G` through a compact open subgroup** (source `quotDesc`): let
`j : H →* G` be a closed embedding, `K` a compact open subgroup of `G`, `S = j(T)` for a closed
subgroup `T` of `H`, with corresponding right-invariant measures `μS`, `μT`, and compatible quotient
measures `νS`, `νT`. For a measurable left `S`-invariant `Φ` on `G` supported in `j(H) K` whose
descent is `νS`-integrable,
`∫_{S\G} Φ dνS = μH(K ∩ H)⁻¹ ∫_{T\H} Ψ dνT` with `Ψ h = ∫_K Φ (j(h) κ) dμG(κ)`. -/
theorem IsCompatible.integral_descend_eq_of_compactOpen (j : H →* G)
    (hj : IsClosedEmbedding j)
    {μG : Measure G} [μG.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μG]
    {μH : Measure H} [μH.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    {S : Subgroup G} {T : Subgroup H} (hT : IsClosed (T : Set H)) (hS : S = T.map j)
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    {μS : Measure S} [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    [μS.IsOpenPosMeasure]
    {μT : Measure T} [μT.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μT]
    [μT.IsOpenPosMeasure]
    (hmap : μS.map Subtype.val = μT.map fun t : T => j t)
    [MeasurableSpace (LeftQuotient S)] [BorelSpace (LeftQuotient S)]
    [MeasurableSpace (LeftQuotient T)] [BorelSpace (LeftQuotient T)]
    {νS : Measure (LeftQuotient S)} (hνS : IsCompatible S μG μS νS)
    {νT : Measure (LeftQuotient T)} (hνT : IsCompatible T μH μT νT)
    (Φ : G → ℂ) (hΦm : Measurable Φ) (hΦS : ∀ s : S, ∀ g, Φ (s.val * g) = Φ g)
    (hsupp : ∀ g, Φ g ≠ 0 → ∃ h : H, ∃ κ ∈ K, g = j h * κ)
    (hint : Integrable (descend S Φ hΦS) νS)
    (Ψ : H → ℂ) (hΨ : ∀ h, Ψ h = ∫ κ in (K : Set G), Φ (j h * κ) ∂μG)
    (hΨT : ∀ t : T, ∀ h, Ψ (t.val * h) = Ψ h) :
    ∫ q, descend S Φ hΦS q ∂νS =
      (μH (K.comap j)).toReal⁻¹ • ∫ q, descend T Ψ hΨT q ∂νT := by
  classical
  have : LocallyCompactSpace T := hT.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set H)
  have : SFinite μT := inferInstance
  have hSc : IsClosed (S : Set G) := by
    rw [hS, Subgroup.coe_map]
    exact hj.isClosedMap _ hT
  have : LocallyCompactSpace S := hSc.locallyCompactSpace
  have hjc : Continuous j := hj.continuous
  have hKm : MeasurableSet (K : Set G) := hKo.measurableSet
  obtain ⟨ρ, hρc, hρ, -⟩ := exists_continuous_isNormalizingFunction T hT μT
  obtain ⟨ρ₀, hρ₀c, hρ₀, -⟩ := exists_continuous_isNormalizingFunction S hSc μS
  have hρm : Measurable ρ := hρc.measurable
  set c : ℝ≥0∞ := μH (K.comap j) with hc
  have hc0 : c ≠ 0 :=
    (hKo.preimage hjc).measure_ne_zero μH ⟨1, by simp⟩
  have hctop : c ≠ ⊤ := (hj.isCompact_preimage hKc).measure_lt_top.ne
  set b := compactOpenDensity j μH ρ K with hbdef
  have hb : Measurable b := measurable_compactOpenDensity hjc μH hρm hKm
  set U : Set G := {g | ∃ h : H, ∃ κ ∈ K, g = j h * κ} with hUdef
  have hUo : IsOpen U := by
    have hU : U = Set.range j * (K : Set G) := by
      ext g
      simp only [hUdef, Set.mem_ofPred_eq, Set.mem_mul, Set.mem_range, SetLike.mem_coe]
      constructor
      · rintro ⟨h, κ, hκ, rfl⟩
        exact ⟨j h, ⟨h, rfl⟩, κ, hκ, rfl⟩
      · rintro ⟨_, ⟨h, rfl⟩, κ, hκ, rfl⟩
        exact ⟨h, κ, hκ, rfl⟩
    rw [hU]
    exact hKo.mul_left
  have hmemS : ∀ s : S, ∃ t : T, j t = s.val := by
    intro s
    have hs : s.val ∈ T.map j := hS ▸ s.property
    obtain ⟨t, ht, e⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨t, ht⟩, e⟩
  have hUS : ∀ s : S, ∀ g, s.val * g ∈ U ↔ g ∈ U := by
    intro s g
    obtain ⟨t, ht⟩ := hmemS s
    constructor
    · rintro ⟨h, κ, hκ, e⟩
      refine ⟨t.val⁻¹ * h, κ, hκ, ?_⟩
      rw [map_mul, map_inv, ht, mul_assoc, ← e]
      group
    · rintro ⟨h, κ, hκ, rfl⟩
      exact ⟨t.val * h, κ, hκ, by rw [map_mul, ht, mul_assoc]⟩
  have hbU : ∀ g, g ∉ U → b g = 0 := by
    intro g hg
    refine compactOpenDensity_eq_zero fun h hh => hg ⟨h, (j h)⁻¹ * g, hh, ?_⟩
    group
  have hΦU : ∀ g, g ∉ U → Φ g = 0 := by
    intro g hg
    by_contra h0
    exact hg (hsupp g h0)
  have hbS : ∀ g ∈ U, ∫⁻ s : S, b (s.val * g) ∂μS = c := by
    rintro g ⟨h₀, κ₀, hκ₀, rfl⟩
    have hbm : Measurable fun x : G => b (x * (j h₀ * κ₀)) := hb.comp (measurable_mul_const _)
    calc ∫⁻ s : S, b (s.val * (j h₀ * κ₀)) ∂μS
        = ∫⁻ x, b (x * (j h₀ * κ₀)) ∂(μS.map Subtype.val) :=
          (lintegral_map hbm continuous_subtype_val.measurable).symm
      _ = ∫⁻ x, b (x * (j h₀ * κ₀)) ∂(μT.map fun t : T => j t) := by rw [hmap]
      _ = ∫⁻ t : T, b (j t * (j h₀ * κ₀)) ∂μT :=
          lintegral_map hbm (hjc.comp continuous_subtype_val).measurable
      _ = c := lintegral_compactOpenDensity_eq hjc μH μT hρm hρ hKm h₀ hκ₀
  -- the glued normalizing function of `S`
  let ρG : G → ℝ≥0∞ := U.piecewise (fun g => b g / c) fun g => (ρ₀ g : ℝ≥0∞)
  have hρG : IsNormalizingFunction S μS ρG := by
    refine ⟨Measurable.piecewise hUo.measurableSet (hb.div_const c)
      hρ₀c.measurable.coe_nnreal_ennreal, fun g => ?_⟩
    by_cases hg : g ∈ U
    · have e : ∀ s : S, ρG (s.val * g) = b (s.val * g) / c := fun s =>
        Set.piecewise_eq_of_mem _ _ _ ((hUS s g).mpr hg)
      simp_rw [e, div_eq_mul_inv]
      have hm : Measurable fun s : S => b (s.val * g) :=
        hb.comp (continuous_subtype_val.mul_const g).measurable
      rw [lintegral_mul_const _ hm, hbS g hg, ENNReal.mul_inv_cancel hc0 hctop]
    · have e : ∀ s : S, ρG (s.val * g) = ρ₀ (s.val * g) := fun s =>
        Set.piecewise_eq_of_notMem _ _ _ (fun h => hg ((hUS s g).mp h))
      simp_rw [e]
      exact hρ₀.lintegral_eq_one g
  have hpt : ∀ g, (b g).toReal • Φ g = c.toReal • ((ρG g).toReal • Φ g) := by
    intro g
    by_cases hg : g ∈ U
    · have e : ρG g = b g / c := Set.piecewise_eq_of_mem _ _ _ hg
      rw [e, smul_smul, ENNReal.toReal_div, mul_div_cancel₀ _
        (ENNReal.toReal_ne_zero.mpr ⟨hc0, hctop⟩)]
    · simp [hΦU g hg]
  have hfin : ∀ᵐ g ∂μG, b g < ⊤ := by
    filter_upwards [hρG.ae_lt_top hSc hνS] with g hg
    by_cases hgU : g ∈ U
    · have e : ρG g = b g / c := Set.piecewise_eq_of_mem _ _ _ hgU
      rw [e] at hg
      have : b g = b g / c * c := (ENNReal.div_mul_cancel hc0 hctop).symm
      rw [this]
      exact ENNReal.mul_lt_top hg hctop.lt_top
    · rw [hbU g hgU]
      exact ENNReal.zero_lt_top
  have hm : Measurable fun p : H × G => j p.1 * p.2 :=
    ((hjc.comp continuous_fst).mul continuous_snd).measurable
  have hW := withDensity_compactOpenDensity hjc μG μH hρm hKm
  -- integrability on the product
  have hintG : Integrable (fun g => (b g).toReal • Φ g) μG := by
    have h1 := (hνS.integrable_descend_iff hSc hρG Φ hΦm hΦS).mp hint
    simp_rw [hpt]
    exact Integrable.smul (μ := μG) c.toReal h1
  have hintW : Integrable Φ (μG.withDensity b) :=
    (integrable_withDensity_iff_integrable_smul' hb hfin).mpr hintG
  rw [hW] at hintW
  have hintP : Integrable (fun p : H × G => Φ (j p.1 * p.2))
      ((μH.withDensity fun h => (ρ h : ℝ≥0∞)).prod (μG.restrict K)) :=
    (integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).mp hintW
  -- the computation
  rw [hνS.integral_descend_eq hSc hρG Φ hΦm hΦS, hνT.integral_descend_eq hT hρ Ψ ?_ hΨT]
  · have e1 : ∀ g, (ρG g).toReal • Φ g = c.toReal⁻¹ • ((b g).toReal • Φ g) := by
      intro g
      rw [hpt, smul_smul, inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hc0, hctop⟩), one_smul]
    simp_rw [e1]
    rw [integral_smul, ← integral_withDensity_eq_integral_toReal_smul hb hfin, hW,
      integral_map hm.aemeasurable hΦm.aestronglyMeasurable, integral_prod (fun p : H × G => Φ (j p.1 * p.2)) hintP]
    congr 1
    rw [integral_withDensity_eq_integral_smul hρm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hΨ h, NNReal.smul_def, ENNReal.coe_toReal]
  · have hf : StronglyMeasurable fun p : H × G => Φ (j p.1 * p.2) :=
      (hΦm.comp hm).stronglyMeasurable
    have := (hf.integral_prod_right' (ν := μG.restrict K)).measurable
    simpa only [← hΨ] using this

end CompactOpen

end Langlands.QuotientIntegration
