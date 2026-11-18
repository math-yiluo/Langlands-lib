import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviCompactWeightComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientBound

/-! # Original compact integrals with an arbitrary source Levi compact -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe u

section WeightAverage

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {K P₀ : Subgroup G} [CompactSpace K]
  {hP₀K : IsIwasawaPair P₀ K} {δ₀ : P₀ →* ℝ≥0ˣ}

/-- Averaging the original weight after a fixed left factor is scalar
multiplication of the original spherical function. The order of the three
factors is retained exactly. -/
theorem integral_iwasawaWeight_mul_mul
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (a g : G) :
    (∫ k : K, iwasawaWeight hP₀K δ₀ (a * ((k : G) * g)) ∂(normalizedHaar K)) =
      iwasawaWeight hP₀K δ₀ a * xi hP₀K δ₀ g := by
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hP₀K a
  generalize iwasawaFactor hP₀K a = q at hfac
  have hpt : ∀ k : K, iwasawaWeight hP₀K δ₀ (a * ((k : G) * g)) =
      NNReal.sqrt (δ₀ q : ℝ≥0) * iwasawaWeight hP₀K δ₀ (k' * ((k : G) * g)) := by
    intro k
    rw [hfac, mul_assoc, iwasawaWeight_mul_left hδ₀ q]
  have hinv := integral_mul_left_eq_self (μ := normalizedHaar K)
    (fun k : K => iwasawaWeight hP₀K δ₀ ((k : G) * g)) ⟨k', hk'⟩
  simp only [Subgroup.coe_mul, mul_assoc] at hinv
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hinv]
  have hq : iwasawaWeight hP₀K δ₀ a = NNReal.sqrt (δ₀ q : ℝ≥0) := by
    rw [hfac]
    exact iwasawaWeight_mul hδ₀ q.property hk'
  rw [hq]
  rfl

end WeightAverage

section Levi

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {K P₀ P M : Subgroup G} [CompactSpace K]
  {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}
  (hP₀K : IsIwasawaPair P₀ K) (KM : Subgroup M) [CompactSpace KM]
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (hKo : IsOpen (K : Set G))

/-- The ambient original weight averaged over the displayed source compact,
divided by its fixed positive lower bound there. -/
def sourceLeviXiComparisonConstant : ℝ :=
  (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
    ∫ k : KM, iwasawaWeight hP₀K δ₀ ((k : M) : G) ∂(normalizedHaar KM)

omit [CompactSpace K] in
/-- The comparison constant is strictly positive and independent of the
parabolic point, original compact variable, twist and coefficient section. -/
theorem sourceLeviXiComparisonConstant_pos :
    0 < sourceLeviXiComparisonConstant hP₀K KM hδ₀ hKo := by
  apply mul_pos (inv_pos.mpr (sourceLeviWeightLowerConstant_spec hP₀K δ₀ hδ₀ hKo KM).1)
  have hc : Continuous (fun k : KM => iwasawaWeight hP₀K δ₀ ((k : M) : G)) :=
    (continuous_iwasawaWeight hδ₀ hKo).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hint := hc.integrable_of_hasCompactSupport (μ := normalizedHaar KM)
    (HasCompactSupport.of_compactSpace _)
  rw [integral_pos_iff_support_of_nonneg (fun k => iwasawaWeight_nonneg _) hint]
  have hsupp : Function.support (fun k : KM => iwasawaWeight hP₀K δ₀ ((k : M) : G)) = Set.univ :=
    Set.eq_univ_of_forall fun k => (iwasawaWeight_pos _).ne'
  rw [hsupp, measure_univ]
  exact one_pos

/-- The source spherical weight for an arbitrary displayed Levi compact.
The ambient factorization and its compact group remain the original ones. -/
def arbitraryCompactLeviXiWeight (hPK : IsIwasawaPair P K)
    (hM : IsIwasawaPair (P₀.subgroupOf M) KM) (x : G) : ℝ :=
  NNReal.sqrt (δP (leviComponent hPK mP x) : ℝ≥0) *
    xi hM δ₀M (leviComponent hPK mP x)

include hδ₀ hKo in
omit [CompactSpace K] in
/-- A continuous compact average of the original ambient weight majorizes
the source spherical weight, at the exact chosen original Levi component. -/
theorem LeviData.arbitraryCompactLeviXiWeight_le_average
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hM : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδPKM : ∀ m : M, m ∈ KM → δP m = 1) (x : G) :
    arbitraryCompactLeviXiWeight (mP := mP) (δP := δP) (δ₀M := δ₀M)
      KM (hP₀K.mono hL.le_P₀) hM x ≤
      (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
        ∫ k : KM, iwasawaWeight hP₀K δ₀ (((k : M) : G) * x) ∂(normalizedHaar KM) := by
  set hPK := hP₀K.mono hL.le_P₀
  obtain ⟨k', hk', hx⟩ := exists_iwasawaFactor hPK x
  set q := iwasawaFactor hPK x
  have hpt : ∀ k : KM,
      NNReal.sqrt (δP (mP q) : ℝ≥0) * iwasawaWeight hM δ₀M ((k : M) * mP q) ≤
        (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
          iwasawaWeight hP₀K δ₀ (((k : M) : G) * x) := by
    intro k
    have he : ((k : M) : G) * x = (((k : M) : G) * (q : G)) * k' := by
      rw [hx, mul_assoc]
    rw [he, iwasawaWeight_mul_right hδ₀ _ hk']
    exact hL.iwasawaWeight_le_mul_arbitraryCompact hP₀K δ₀ hδ₀ hKo KM hM hδPKM q k
  have hsrc := (integrable_iwasawaWeight_mul (hPK := hM) hδ₀M hKMo (mP q)).const_mul
    (NNReal.sqrt (δP (mP q) : ℝ≥0) : ℝ)
  have hc : Continuous (fun k : KM => iwasawaWeight hP₀K δ₀ (((k : M) : G) * x)) :=
    (continuous_iwasawaWeight hδ₀ hKo).comp
      ((continuous_subtype_val.comp continuous_subtype_val).mul continuous_const)
  have htarget := (hc.integrable_of_hasCompactSupport (μ := normalizedHaar KM)
    (HasCompactSupport.of_compactSpace _)).const_mul
      (sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹
  have h := integral_mono hsrc htarget hpt
  rw [integral_const_mul, integral_const_mul] at h
  exact h

variable [SecondCountableTopology G]

include hδ₀ hKo in
/-- The original compact integral is bounded by the original spherical
function even when the source spherical function uses a different compact
Levi subgroup. No measurability of the choice-dependent Levi component is
assumed: a continuous double integral provides the majorant. -/
theorem LeviData.norm_compactIntegral_le_xi_arbitraryCompact
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hM : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδPKM : ∀ m : M, m ∈ KM → δP m = 1)
    {Φ : K → G → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ (k : K) (x : G), ‖Φ k x‖ ≤
      C * arbitraryCompactLeviXiWeight (mP := mP) (δP := δP) (δ₀M := δ₀M)
      KM (hP₀K.mono hL.le_P₀) hM x) (g : G) :
    ‖compactIntegral K Φ g‖ ≤
      (C * sourceLeviXiComparisonConstant hP₀K KM hδ₀ hKo) * xi hP₀K δ₀ g := by
  let : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  let : SecondCountableTopology KM :=
    TopologicalSpace.Subtype.secondCountableTopology (KM : Set M)
  let μ := normalizedHaar K
  let ν := normalizedHaar KM
  let F : KM → K → ℝ := fun kM k =>
    iwasawaWeight hP₀K δ₀ (((kM : M) : G) * ((k : G) * g))
  have hFc : Continuous (Function.uncurry F) :=
    (continuous_iwasawaWeight hδ₀ hKo).comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
  have hFi : Integrable (Function.uncurry F) (ν.prod μ) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hFi
  have he : (∫ k : K, ∫ kM : KM, F kM k ∂ν ∂μ) =
      (∫ kM : KM, iwasawaWeight hP₀K δ₀ ((kM : M) : G) ∂ν) * xi hP₀K δ₀ g := by
    rw [← hswap]
    simp_rw [show ∀ kM : KM, (∫ k : K, F kM k ∂μ) =
      iwasawaWeight hP₀K δ₀ ((kM : M) : G) * xi hP₀K δ₀ g from
        fun kM => integral_iwasawaWeight_mul_mul hδ₀ _ g]
    rw [integral_mul_const]
  have hb : ∀ k : K, ‖Φ k ((k : G) * g)‖ ≤
      C * ((sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
        ∫ kM : KM, F kM k ∂ν) := fun k => (hΦ k _).trans
      (mul_le_mul_of_nonneg_left
        (hL.arbitraryCompactLeviXiWeight_le_average hP₀K KM hδ₀ hKo hM hKMo hδ₀M hδPKM _) hC)
  calc ‖compactIntegral K Φ g‖ ≤ ∫ k : K,
      C * ((sourceLeviWeightLowerConstant hP₀K δ₀ hδ₀ hKo KM)⁻¹ *
        ∫ kM : KM, F kM k ∂ν) ∂μ :=
        norm_integral_le_of_norm_le
          ((hFi.integral_prod_right.const_mul _).const_mul C) (Filter.Eventually.of_forall hb)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, he]
      unfold sourceLeviXiComparisonConstant
      ring

end Levi

end Langlands.HarishChandraSchwartz
