import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi

/-! # A lower spherical bound from a contracting open subgroup -/

noncomputable section

open MeasureTheory Measure
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {K P₀ P M : Subgroup G} [CompactSpace K] [CompactSpace (K.subgroupOf M)]
  {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}

/-- Suppose one open subgroup has a factorization with an opposite
factor contracted into `K` by the displayed Levi points. Then ambient Xi
bounds the normalized Levi Xi there, by the reciprocal of the open subgroup's
Haar mass. Only the parabolic projection on that open subgroup is used. -/
theorem LeviData.exists_sqrt_mul_xi_le_xi_of_factorization
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP) (hKo : IsOpen (K : Set G))
    (hP₀K : IsIwasawaPair P₀ K) (hMK : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    {H : Subgroup G} (hHo : IsOpen (H : Set G)) {V : Set G} {S : Set M}
    (hfac : ∀ k ∈ H, ∃ p : P, (p : G) ∈ H ∧ ∃ v ∈ V, k = (p : G) * v)
    (hsmall : ∀ p : P, (p : G) ∈ H → (mP p : G) ∈ K)
    (hcontract : ∀ (m : M), m ∈ S → ∀ v ∈ V, (m : G)⁻¹ * v * (m : G) ∈ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ S,
      (NNReal.sqrt (δP m : ℝ≥0) : ℝ) * xi hMK δ₀M m ≤ C * xi hP₀K δ₀ (m : G) := by
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  let : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  let : SecondCountableTopology (K.subgroupOf M) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ := normalizedHaar K
  let η := normalizedHaar (K.subgroupOf M)
  let X : Set K := {k | (k : G) ∈ H}
  have hXo : IsOpen X := hHo.preimage continuous_subtype_val
  have hXp : 0 < μ.real X := ENNReal.toReal_pos
    (hXo.measure_pos μ ⟨1, H.one_mem⟩).ne' (measure_ne_top _ _)
  refine ⟨(μ.real X)⁻¹, inv_pos.mpr hXp, fun m hm => ?_⟩
  let w₀ := iwasawaWeight hP₀K δ₀
  let F : K → K.subgroupOf M → ℝ := fun k l => w₀ (((l : M) : G) * ((k : G) * (m : G)))
  have hFc : Continuous (Function.uncurry F) :=
    (continuous_iwasawaWeight (hPK := hP₀K) hδ₀ hKo).comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  have hFi : Integrable (Function.uncurry F) (μ.prod η) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have houter (l : K.subgroupOf M) : (∫ k, F k l ∂μ) = xi hP₀K δ₀ (m : G) := by
    have hl : ((l : M) : G) ∈ K := Subgroup.mem_subgroupOf.mp l.property
    have he := integral_mul_left_eq_self (μ := μ) (fun k : K => w₀ ((k : G) * (m : G))) ⟨_, hl⟩
    simpa only [Subgroup.coe_mul, mul_assoc, F] using (show _ = xi hP₀K δ₀ (m : G) from he)
  have hXi : (∫ k, ∫ l, F k l ∂η ∂μ) = xi hP₀K δ₀ (m : G) := by
    rw [integral_integral_swap hFi]
    simp only [houter]
    simp [η]
  let W := (NNReal.sqrt (δP m : ℝ≥0) : ℝ) * xi hMK δ₀M m
  have hinner (k : K) (hk : k ∈ X) : (∫ l, F k l ∂η) = W := by
    obtain ⟨p, hp, v, hv, hkv⟩ := hfac (k : G) hk
    let p' := p * Subgroup.inclusion hL.le_M m
    have hproj : mP p' = mP p * m := by rw [map_mul, hL.apply_inclusion]
    have hpt (l : K.subgroupOf M) : F k l =
        NNReal.sqrt (δP (mP p') : ℝ≥0) * iwasawaWeight hMK δ₀M ((l : M) * mP p') := by
      have he : ((l : M) : G) * ((k : G) * (m : G)) =
          (((l : M) : G) * (p' : G)) * ((m : G)⁻¹ * v * (m : G)) := by
        rw [hkv]
        change _ = (((l : M) : G) * ((p : G) * (m : G))) * ((m : G)⁻¹ * v * (m : G))
        group
      change iwasawaWeight hP₀K δ₀ _ = _
      rw [he, iwasawaWeight_mul_right hδ₀ _ (hcontract m hm v hv)]
      exact hL.iwasawaWeight_mul hP₀K hMK hδ₀ p' l
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    change (NNReal.sqrt (δP (mP p') : ℝ≥0) : ℝ) * xi hMK δ₀M (mP p') = W
    rw [hproj, map_mul, hL.δP_of_mem _ (hsmall p hp), one_mul,
      xi_mul_left (Subgroup.mem_subgroupOf.mpr (hsmall p hp))]
  have hlower : μ.real X * W ≤ xi hP₀K δ₀ (m : G) := by
    calc μ.real X * W = ∫ k in X, ∫ l, F k l ∂η ∂μ := by
          rw [setIntegral_congr_fun hXo.measurableSet hinner, setIntegral_const, smul_eq_mul]
      _ ≤ ∫ k, ∫ l, F k l ∂η ∂μ := setIntegral_le_integral hFi.integral_prod_left
        (Filter.Eventually.of_forall fun k => integral_nonneg fun l => iwasawaWeight_nonneg _)
      _ = _ := hXi
  change W ≤ (μ.real X)⁻¹ * xi hP₀K δ₀ (m : G)
  rw [inv_mul_eq_div, le_div_iff₀ hXp, mul_comm]
  exact hlower

end Langlands.HarishChandraSchwartz
