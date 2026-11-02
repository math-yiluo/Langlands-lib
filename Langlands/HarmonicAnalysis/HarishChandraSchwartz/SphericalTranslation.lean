import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalInverse
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrability
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations

/-! # Translation bounds for the spherical function `Ξ`

Waldspurger 2003, Lemma II.1.2: there is `d ∈ ℕ` such that for all `g₁, g₂ ∈ G` there is
`C` with `Ξ(g₁ g g₂) ≤ C Ξ(g) (1 + σ(g))^d` for all `g ∈ G`. For the function `xi` of
`Spherical` this module proves the bound with `d = 0`, from Lemma II.1.3
(`integral_xi_mul_mul`) and the bi-`K`-invariance of `Ξ`: for `k` in the open subgroup
`K ∩ g₁⁻¹ K g₁` of `K` one has `Ξ(g₁ k g) = Ξ(g₁ g)`, so
`mes(K ∩ g₁⁻¹ K g₁) Ξ(g₁ g) ≤ ∫_K Ξ(g₁ k g) dk = Ξ(g₁) Ξ(g)`, and similarly on the right.
It then assembles the hypotheses `TranslationWeights` and `ConvolutionWeights` of the
generic translation and convolution results for `Ξ = xi`.
-/

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Statement

variable {G : Type u} [Group G]

/-- Uniform comparability of `Ξ` under translations: for all `g₁, g₂ ∈ G` there is `C`
with `Ξ(g₁ g g₂) ≤ C Ξ(g)` for all `g ∈ G`. This is the conclusion of Lemma II.1.2 of
Waldspurger with exponent `d = 0`. -/
def UniformTranslationBound (Ξ : G → ℝ) : Prop :=
  ∀ g₁ g₂ : G, ∃ C : ℝ, ∀ g : G, Ξ (g₁ * g * g₂) ≤ C * Ξ g

variable {Ξ : G → ℝ}

/-- The uniform bound gives Lemma II.1.2 (`TranslationBound`) with `d = 0`, for every
`σ`. -/
theorem UniformTranslationBound.translationBound (h : UniformTranslationBound Ξ)
    (σ : G → ℝ) : TranslationBound Ξ σ :=
  ⟨0, fun g₁ g₂ => (h g₁ g₂).imp fun C hC g => by simpa using hC g⟩

/-- The reverse inequality: for all `g₁, g₂` there is `C` with `Ξ(g) ≤ C Ξ(g₁ g g₂)` for
all `g`. -/
theorem UniformTranslationBound.exists_le_mul (h : UniformTranslationBound Ξ) (g₁ g₂ : G) :
    ∃ C : ℝ, ∀ g : G, Ξ g ≤ C * Ξ (g₁ * g * g₂) := by
  obtain ⟨C, hC⟩ := h g₁⁻¹ g₂⁻¹
  refine ⟨C, fun g => ?_⟩
  have e := hC (g₁ * g * g₂)
  rwa [show g₁⁻¹ * (g₁ * g * g₂) * g₂⁻¹ = g by group] at e

end Statement

section Spherical

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {P K : Subgroup G} [CompactSpace K]

omit [MeasurableSpace G] [BorelSpace G] [CompactSpace K] in
/-- For `a, b ∈ G`, the set of `k ∈ K` with `a k b ∈ K` is open in `K`. -/
theorem isOpen_setOf_mul_mul_mem (hK : IsOpen (K : Set G)) (a b : G) :
    IsOpen {k : K | a * (k : G) * b ∈ K} :=
  hK.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- For `a, b ∈ G` with `a b ∈ K`, the set of `k ∈ K` with `a k b ∈ K` has positive
measure for the Haar measure of `K` of total mass one. -/
theorem measureReal_setOf_mul_mul_mem_pos (hK : IsOpen (K : Set G))
    {a b : G} (hab : a * b ∈ K) :
    0 < (normalizedHaar K).real {k : K | a * (k : G) * b ∈ K} := by
  have hne : ({k : K | a * (k : G) * b ∈ K} : Set K).Nonempty :=
    ⟨1, by simpa using hab⟩
  rw [measureReal_def]
  exact ENNReal.toReal_pos ((isOpen_setOf_mul_mul_mem hK a b).measure_pos _ hne).ne'
    (measure_ne_top _ _)

variable [SecondCountableTopology G] {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1) (hK : IsOpen (K : Set G))
include hδ hK

/-- If `Ξ(g₁ k g₂) = Ξ(g₁ g₂)` for all `k` in a measurable subset `S` of `K`, then
`mes(S) Ξ(g₁ g₂) ≤ Ξ(g₁) Ξ(g₂)`, by Lemma II.1.3. -/
theorem measureReal_mul_xi_le (g₁ g₂ : G) {S : Set K} (hS : MeasurableSet S)
    (hSK : ∀ k ∈ S, xi hPK δ (g₁ * k * g₂) = xi hPK δ (g₁ * g₂)) :
    (normalizedHaar K).real S * xi hPK δ (g₁ * g₂) ≤ xi hPK δ g₁ * xi hPK δ g₂ := by
  have hc : Continuous fun k : K => xi hPK δ (g₁ * k * g₂) :=
    (continuous_xi hδ hK).comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hi : Integrable (fun k : K => xi hPK δ (g₁ * k * g₂)) (normalizedHaar K) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc (normalizedHaar K).real S * xi hPK δ (g₁ * g₂)
      = ∫ k in S, xi hPK δ (g₁ * k * g₂) ∂(normalizedHaar K) := by
        rw [setIntegral_congr_fun hS (fun k hk => hSK k hk), setIntegral_const, smul_eq_mul]
    _ ≤ ∫ k : K, xi hPK δ (g₁ * k * g₂) ∂(normalizedHaar K) :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall fun k => (xi_pos hδ hK _).le)
    _ = xi hPK δ g₁ * xi hPK δ g₂ := integral_xi_mul_mul hδ hK g₁ g₂

/-- Left translations: `Ξ(g₁ g) ≤ Ξ(g₁) / mes(K ∩ g₁⁻¹ K g₁) · Ξ(g)`. -/
theorem xi_mul_le_left (g₁ g : G) :
    xi hPK δ (g₁ * g) ≤
      xi hPK δ g₁ / (normalizedHaar K).real {k : K | g₁ * (k : G) * g₁⁻¹ ∈ K} * xi hPK δ g := by
  have hpos := measureReal_setOf_mul_mul_mem_pos hK (a := g₁) (b := g₁⁻¹)
    (by simp)
  have h := measureReal_mul_xi_le (hPK := hPK) hδ hK g₁ g
    (isOpen_setOf_mul_mul_mem hK g₁ g₁⁻¹).measurableSet fun k hk => by
      have e : g₁ * (k : G) * g = (g₁ * k * g₁⁻¹) * (g₁ * g) := by group
      rw [e, xi_mul_left hk]
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- Right translations: `Ξ(g g₂) ≤ Ξ(g₂) / mes(K ∩ g₂ K g₂⁻¹) · Ξ(g)`. -/
theorem xi_mul_le_right (g g₂ : G) :
    xi hPK δ (g * g₂) ≤
      xi hPK δ g₂ / (normalizedHaar K).real {k : K | g₂⁻¹ * (k : G) * g₂ ∈ K} * xi hPK δ g := by
  have hpos := measureReal_setOf_mul_mul_mem_pos hK (a := g₂⁻¹) (b := g₂)
    (by simp)
  have h := measureReal_mul_xi_le (hPK := hPK) hδ hK g g₂
    (isOpen_setOf_mul_mul_mem hK g₂⁻¹ g₂).measurableSet fun k hk => by
      have e : g * (k : G) * g₂ = (g * g₂) * (g₂⁻¹ * k * g₂) := by group
      rw [e, xi_mul_right hδ _ hk]
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- **Waldspurger, Lemma II.1.2**, with `d = 0`: for all `g₁, g₂ ∈ G` there is `C` with
`Ξ(g₁ g g₂) ≤ C Ξ(g)` for all `g ∈ G`. -/
theorem xi_uniformTranslationBound : UniformTranslationBound (xi hPK δ) := by
  intro g₁ g₂
  set C₁ := xi hPK δ g₁ / (normalizedHaar K).real {k : K | g₁ * (k : G) * g₁⁻¹ ∈ K}
  set C₂ := xi hPK δ g₂ / (normalizedHaar K).real {k : K | g₂⁻¹ * (k : G) * g₂ ∈ K}
  have hC₁ : 0 ≤ C₁ := div_nonneg (xi_pos hδ hK _).le measureReal_nonneg
  refine ⟨C₁ * C₂, fun g => ?_⟩
  calc xi hPK δ (g₁ * g * g₂) = xi hPK δ (g₁ * (g * g₂)) := by rw [mul_assoc]
    _ ≤ C₁ * xi hPK δ (g * g₂) := xi_mul_le_left hδ hK g₁ (g * g₂)
    _ ≤ C₁ * (C₂ * xi hPK δ g) :=
        mul_le_mul_of_nonneg_left (xi_mul_le_right hδ hK g g₂) hC₁
    _ = C₁ * C₂ * xi hPK δ g := by ring

/-- Lemma II.1.2 for `Ξ = xi` in the form `TranslationBound` of `Translations`, with
`d = 0`, for every `σ`. -/
theorem xi_translationBound (σ : G → ℝ) : TranslationBound (xi hPK δ) σ :=
  (xi_uniformTranslationBound hδ hK).translationBound σ

/-- The hypotheses `TranslationWeights` of the generic translation results hold for
`Ξ = xi` and every nonnegative `σ` satisfying the translation bound for heights. -/
theorem xi_translationWeights {σ : G → ℝ} (hσ : ∀ g, 0 ≤ σ g)
    (hσt : HeightTranslationBound σ) : TranslationWeights (xi hPK δ) σ :=
  ⟨xi_pos hδ hK, hσ, xi_translationBound hδ hK σ, hσt⟩

end Spherical

section Convolution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {P K : Subgroup G} [LocallyCompactSpace P] [CompactSpace K]
  {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}

/-- The hypotheses `ConvolutionWeights` of the generic Lemma III.6.1 hold for `Ξ = xi`,
when `G` is unimodular, `P` is closed, `K` is open, `δ` is the modular character of `P`,
`σ` is nonnegative, continuous, subadditive and left `K`-invariant, and Lemma II.1.5
(`SquareIntegrableWeight`) holds for `μ`, `xi` and `σ`. -/
theorem xi_convolutionWeights (hG : ∀ g : G, modularCharacter g = 1)
    (hP : IsClosed (P : Set G)) (hK : IsOpen (K : Set G))
    (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p) {μ : Measure G} {σ : G → ℝ}
    (hσ : ∀ g, 0 ≤ σ g) (hσc : Continuous σ) (hadd : ∀ g h, σ (g * h) ≤ σ g + σ h)
    (hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g) (hsq : SquareIntegrableWeight μ (xi hPK δ) σ) :
    ConvolutionWeights μ K (xi hPK δ) σ where
  pos := xi_pos (modular_eq_one_of_mem hP hK hδ) hK
  nonneg := hσ
  continuous_xi := continuous_xi (modular_eq_one_of_mem hP hK hδ) hK
  continuous_sigma := hσc
  one_add_le := one_add_le_of_le_add hσ hadd
  xi_mul_left := fun _ hk g => xi_mul_left hk g
  sigma_mul_left := hσK
  xi_inv := xi_inv hG hP hK hδ
  integral_xi := integral_xi_mul_mul (modular_eq_one_of_mem hP hK hδ) hK
  square := hsq

end Convolution

end Langlands.HarishChandraSchwartz
