import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi

/-! # Comparing Levi Iwasawa weights for an arbitrary compact source subgroup -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Weights

variable {G : Type u} [Group G] {K P₀ P M : Subgroup G}
  {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}
  (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
  (hP₀K : IsIwasawaPair P₀ K) (KM : Subgroup M)
  (hM : IsIwasawaPair (P₀.subgroupOf M) KM)
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
  (hδPKM : ∀ m : M, m ∈ KM → δP m = 1)

include hL hδ₀ hδPKM in
/-- Exact weight factorization with an arbitrary source compact factor.
The final factor is the original ambient weight at the actual source
Iwasawa compact factor, rather than an assumed value one. -/
theorem LeviData.iwasawaWeight_mul_arbitraryCompact (p : P) (kM : KM) :
    ∃ k' ∈ KM,
      iwasawaWeight hP₀K δ₀ (((kM : M) : G) * p) =
        NNReal.sqrt (δP (mP p) : ℝ≥0) * iwasawaWeight hM δ₀M ((kM : M) * mP p) *
          iwasawaWeight hP₀K δ₀ ((k' : M) : G) := by
  set m : M := mP p with hm
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hM ((kM : M) * m)
  set a := iwasawaFactor hM ((kM : M) * m) with ha
  -- `v = k' m⁻¹ p k'⁻¹` lies in `P` and in the kernel of `m_P`
  set v : P := Subgroup.inclusion hL.le_M k' * (Subgroup.inclusion hL.le_M m)⁻¹ * p *
    (Subgroup.inclusion hL.le_M k')⁻¹ with hv
  have hmv : mP v = 1 := by
    simp only [hv, map_mul, map_inv, hL.apply_inclusion, hm, inv_mul_cancel_right,
      mul_inv_cancel]
  have hvP₀ : (v : G) ∈ P₀ := hL.mem_of_apply_eq_one v hmv
  have haP₀ : ((a : M) : G) ∈ P₀ := a.2
  -- the factorization `k_M p = (a v) k'`
  have hfacG : ((kM : M) : G) * p = (((a : M) : G) * v) * ((k' : M) : G) := by
    have h1 : ((kM : M) : G) = ((a : M) : G) * ((k' : M) : G) * ((m : M) : G)⁻¹ := by
      have := congrArg (fun x : M => (x : G)) hfac
      simp only [Subgroup.coe_mul] at this
      rw [eq_mul_inv_iff_mul_eq, this]
    rw [h1, hv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  refine ⟨k', hk', ?_⟩
  rw [hfacG, iwasawaWeight_mul_left hδ₀
    (⟨((a : M) : G) * v, P₀.mul_mem haP₀ hvP₀⟩ : P₀)]
  -- evaluate `δ₀(a v) = δ_P(m) δ₀^M(a)`
  have hδv : δ₀ ⟨v, hvP₀⟩ = 1 := by
    refine hL.δ₀_of_apply_eq_one _ ?_
    have : Subgroup.inclusion hL.le_P₀ ⟨(v : G), hvP₀⟩ = v := Subtype.ext rfl
    rw [this, hmv]
  have hδa : δ₀ ⟨((a : M) : G), haP₀⟩ = δP m * δ₀M a := by
    rw [hL.δ₀_of_mem ⟨((a : M) : G), haP₀⟩ (a : M).2]
    have hδPa : δP (a : M) = δP m := by
      have h2 : (a : M) = (kM : M) * m * k'⁻¹ := by
        rw [hfac, mul_inv_cancel_right]
      rw [h2, map_mul, map_mul, map_inv, hδPKM _ kM.property,
        hδPKM _ hk', one_mul, inv_one, mul_one]
    rw [← hδPa]
  have hmul : (⟨((a : M) : G) * v, P₀.mul_mem haP₀ hvP₀⟩ : P₀) =
      ⟨((a : M) : G), haP₀⟩ * ⟨v, hvP₀⟩ := rfl
  rw [hmul, map_mul, hδv, mul_one, hδa]
  change NNReal.sqrt (δP m * δ₀M a : ℝ≥0) *
    iwasawaWeight hP₀K δ₀ ((k' : M) : G) = _
  have hw : iwasawaWeight hM δ₀M ((kM : M) * m) = NNReal.sqrt (δ₀M a : ℝ≥0) := rfl
  rw [hw]
  simp only [NNReal.sqrt_mul, NNReal.coe_mul]

end Weights

section CompactLower

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K P₀ M : Subgroup G} (hP₀K : IsIwasawaPair P₀ K) (δ₀ : P₀ →* ℝ≥0ˣ)
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (hKo : IsOpen (K : Set G))
  (KM : Subgroup M) [CompactSpace KM]

include hδ₀ hKo in
/-- Positivity and continuity give one positive lower weight on the entire
original displayed compact source subgroup. -/
theorem exists_sourceLeviWeight_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ k : M, k ∈ KM → c ≤ iwasawaWeight hP₀K δ₀ ((k : M) : G) := by
  have hw : Continuous (fun k : KM => iwasawaWeight hP₀K δ₀ ((k : M) : G)) :=
    (continuous_iwasawaWeight hδ₀ hKo).comp (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨k, -, hk⟩ := (isCompact_univ : IsCompact (Set.univ : Set KM)).exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set KM).Nonempty) hw.continuousOn
  exact ⟨iwasawaWeight hP₀K δ₀ ((k : M) : G), iwasawaWeight_pos _, fun l hl => hk (Set.mem_univ ⟨l, hl⟩)⟩

/-- A positive lower bound for the original ambient weight on the chosen
source compact subgroup, fixed before all parabolic points. -/
def sourceLeviWeightLowerConstant : ℝ :=
  Classical.choose (exists_sourceLeviWeight_lower hP₀K δ₀ hδ₀ hKo KM)

/-- The selected constant is positive and bounds every displayed compact
source point from below. -/
theorem sourceLeviWeightLowerConstant_spec :
    0 < sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM ∧
    ∀ k : M, k ∈ KM → sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM ≤
      iwasawaWeight hP₀K δ₀ ((k : M) : G) :=
  Classical.choose_spec (exists_sourceLeviWeight_lower hP₀K δ₀ hδ₀ hKo KM)

/-- Uniform pointwise comparison with the actual original ambient weight,
for an arbitrary compact source Iwasawa subgroup. -/
theorem LeviData.iwasawaWeight_le_mul_arbitraryCompact
    {P : Subgroup G} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hM : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hδPKM : ∀ m : M, m ∈ KM → δP m = 1) (p : P) (kM : KM) :
    NNReal.sqrt (δP (mP p) : ℝ≥0) * iwasawaWeight hM δ₀M ((kM : M) * mP p) ≤
      (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
        iwasawaWeight hP₀K δ₀ (((kM : M) : G) * p) := by
  obtain ⟨k', hk', he⟩ := hL.iwasawaWeight_mul_arbitraryCompact hP₀K KM hM hδ₀ hδPKM p kM
  obtain ⟨hc0, hc⟩ := sourceLeviWeightLowerConstant_spec hP₀K δ₀ hδ₀ hKo KM
  have hX0 : 0 ≤ NNReal.sqrt (δP (mP p) : ℝ≥0) *
      iwasawaWeight hM δ₀M ((kM : M) * mP p) :=
    mul_nonneg (NNReal.coe_nonneg _) (iwasawaWeight_nonneg _)
  have hb : sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM *
      (NNReal.sqrt (δP (mP p) : ℝ≥0) * iwasawaWeight hM δ₀M ((kM : M) * mP p)) ≤
      iwasawaWeight hP₀K δ₀ (((kM : M) : G) * p) := by
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hc k' hk') hX0
  calc _ = (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
        (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM *
          (NNReal.sqrt (δP (mP p) : ℝ≥0) * iwasawaWeight hM δ₀M ((kM : M) * mP p))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc0.le)

end CompactLower

end Langlands.HarishChandraSchwartz
