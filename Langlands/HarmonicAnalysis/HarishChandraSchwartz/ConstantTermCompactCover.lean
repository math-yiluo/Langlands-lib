import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactComparison

/-! # Extending a constant-term estimate from compact double-coset representatives -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

/-- Two comparable positive bases have comparable real powers in either direction. -/
theorem rpow_le_mul_rpow_of_comparison {a b A : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A)
    (hab : a ≤ A * b) (hba : b ≤ A * a) (r : ℝ) :
    a ^ r ≤ A ^ |r| * b ^ r := by
  by_cases hr : 0 ≤ r
  · simpa only [Real.mul_rpow hA.le hb.le, abs_of_nonneg hr] using
      Real.rpow_le_rpow ha.le hab hr
  · have hr' : r ≤ 0 := le_of_not_ge hr
    have hdiv : b / A ≤ a := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hba)
    calc a ^ r ≤ (b / A) ^ r :=
        Real.rpow_le_rpow_of_nonpos (div_pos hb hA) hdiv hr'
      _ = A ^ |r| * b ^ r := by
        rw [Real.div_rpow hb.le hA.le, abs_of_nonpos hr', Real.rpow_neg hA.le,
          div_eq_mul_inv, mul_comm]

section Kernels

variable {G : Type u} [Group G] {Ξ σ : G → ℝ}

/-- A subadditive symmetric nonnegative height preserves translation bounds
after multiplication by any real power of `1 + σ`. -/
theorem UniformTranslationBound.mul_one_add_rpow (h : UniformTranslationBound Ξ)
    (hΞ : ∀ g, 0 ≤ Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hinv : ∀ g, σ g⁻¹ = σ g) (hsub : ∀ g g', σ (g * g') ≤ σ g + σ g')
    (r : ℝ) :
    UniformTranslationBound (fun g => Ξ g * (1 + σ g) ^ r) := by
  intro a b
  obtain ⟨C, hC⟩ := h a b
  let A := 1 + σ a + σ b
  have hA : 0 < A := by dsimp [A]; linarith [hσ a, hσ b]
  have hcomp (a b g : G) :
      1 + σ (a * g * b) ≤ (1 + σ a + σ b) * (1 + σ g) := by
    have h1 := hsub (a * g) b
    have h2 := hsub a g
    nlinarith [hσ a, hσ b, hσ g]
  refine ⟨max C 0 * A ^ |r|, fun g => ?_⟩
  have hforward : 1 + σ (a * g * b) ≤ A * (1 + σ g) := hcomp a b g
  have hreverse : 1 + σ g ≤ A * (1 + σ (a * g * b)) := by
    have hv := hcomp a⁻¹ b⁻¹ (a * g * b)
    rw [hinv, hinv, show a⁻¹ * (a * g * b) * b⁻¹ = g by group] at hv
    exact hv
  have hpow := rpow_le_mul_rpow_of_comparison
    (by linarith [hσ (a * g * b)]) (by linarith [hσ g])
    hA hforward hreverse r
  have hxi := (hC g).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (hΞ g))
  calc Ξ (a * g * b) * (1 + σ (a * g * b)) ^ r
      ≤ (max C 0 * Ξ g) * (A ^ |r| * (1 + σ g) ^ r) :=
        mul_le_mul hxi hpow (Real.rpow_nonneg (by linarith [hσ (a * g * b)]) _)
          (mul_nonneg (le_max_right C 0) (hΞ g))
    _ = (max C 0 * A ^ |r|) * (Ξ g * (1 + σ g) ^ r) := by ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A translation bound for a nonnegative function locally bi-invariant under
one open subgroup is uniform on both sides of any compact subgroup. -/
theorem UniformTranslationBound.exists_uniform_mul (h : UniformTranslationBound Ξ)
    (hΞ : ∀ g, 0 ≤ Ξ g) {H K : Subgroup G} (hHo : IsOpen (H : Set G))
    (hleft : ∀ k ∈ H, ∀ g, Ξ (k * g) = Ξ g)
    (hright : ∀ k ∈ H, ∀ g, Ξ (g * k) = Ξ g)
    (hKc : IsCompact (K : Set G)) :
    ∃ C : ℝ≥0, ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g,
      Ξ (k₁ * g * k₂) ≤ C * Ξ g := by
  obtain ⟨CL, hCL⟩ := h.exists_uniform_left hΞ hHo hleft hKc
  have hInv : UniformTranslationBound (fun g => Ξ g⁻¹) := by
    intro a b
    obtain ⟨C, hC⟩ := h b⁻¹ a⁻¹
    exact ⟨C, fun g => by simpa only [mul_inv_rev, mul_assoc] using hC g⁻¹⟩
  obtain ⟨CR, hCR⟩ := hInv.exists_uniform_left (fun g => hΞ g⁻¹) hHo
    (fun k hk g => by rw [mul_inv_rev, hright _ (H.inv_mem hk)]) hKc
  have hR (k : G) (hk : k ∈ K) (g : G) : Ξ (g * k) ≤ max CR 0 * Ξ g := by
    have hh := hCR k⁻¹ (K.inv_mem hk) g⁻¹
    simp only [mul_inv_rev, inv_inv] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left CR 0) (hΞ g))
  have hL (k : G) (hk : k ∈ K) (g : G) : Ξ (k * g) ≤ max CL 0 * Ξ g :=
    (hCL k hk g).trans (mul_le_mul_of_nonneg_right (le_max_left CL 0) (hΞ g))
  let C : ℝ≥0 := ⟨max CL 0 * max CR 0, mul_nonneg (le_max_right _ _) (le_max_right _ _)⟩
  refine ⟨C, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
  calc Ξ (k₁ * g * k₂) ≤ max CR 0 * Ξ (k₁ * g) := hR k₂ hk₂ _
    _ ≤ max CR 0 * (max CL 0 * Ξ g) :=
      mul_le_mul_of_nonneg_left (hL k₁ hk₁ g) (le_max_right _ _)
    _ = _ := by change _ = (max CL 0 * max CR 0) * Ξ g; ring

end Kernels

section Cover

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM σM : M → ℝ} {KM : Subgroup M} {S : Set M}

/-- Compact Cartan reduction requires bounded translations of the weighted
kernels; the structural compact subgroup need not preserve their values. -/
theorem constantTermEstimate_of_doubleCosetCover
    (hν : IsConjModulus hMU ν δ) (hδK : ∀ k ∈ KM, δ k = 1)
    (hcover : IsDoubleCosetCover KM S)
    (hGker : ∀ r : ℝ, ∃ A : ℝ≥0, ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g : G,
      Ξ ((k₁ : G) * g * k₂) * (1 + σ ((k₁ : G) * g * k₂)) ^ (-r) ≤
        A * (Ξ g * (1 + σ g) ^ (-r)))
    (hMker : ∀ r : ℝ, ∃ B : ℝ≥0, ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m : M,
      ΞM (k₁ * m * k₂) * (1 + σM (k₁ * m * k₂)) ^ (-r) ≤
        B * (ΞM m * (1 + σM m) ^ (-r)))
    (hS : ∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ s ∈ S,
      (NNReal.sqrt (δ s) : ℝ≥0∞) *
          ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-d')) ∂ν ≤
        c * ENNReal.ofReal (ΞM s * (1 + σM s) ^ (-d))) :
    ConstantTermEstimate ν δ Ξ σ ΞM σM := by
  intro d
  obtain ⟨d', c, hc⟩ := hS d
  obtain ⟨A, hA⟩ := hGker d'
  obtain ⟨B, hB⟩ := hMker d
  refine ⟨d', A * c * B, fun m => ?_⟩
  obtain ⟨k₁, hk₁, s, hs, k₂, hk₂, rfl⟩ := hcover m
  have hδ : δ (k₁ * s * k₂) = δ s := by
    rw [map_mul, map_mul, hδK k₁ hk₁, hδK k₂ hk₂, one_mul, mul_one]
  have hfun (u : U) :
      (((k₁ * s * k₂ : M) : G) * u) =
        (k₁ : G) * ((s : G) * conjUnipotent hMU k₂ u) * k₂ := by
    simp only [conjUnipotent, Subgroup.coe_mul]
    group
  have hint :
      ∫⁻ u : U, ENNReal.ofReal (Ξ (((k₁ * s * k₂ : M) : G) * u) *
        (1 + σ (((k₁ * s * k₂ : M) : G) * u)) ^ (-d')) ∂ν ≤
        (A : ℝ≥0∞) * ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
          (1 + σ ((s : G) * u)) ^ (-d')) ∂ν := by
    calc ∫⁻ u : U, ENNReal.ofReal (Ξ (((k₁ * s * k₂ : M) : G) * u) *
          (1 + σ (((k₁ * s * k₂ : M) : G) * u)) ^ (-d')) ∂ν
        ≤ ∫⁻ u : U, (A : ℝ≥0∞) * ENNReal.ofReal
          (Ξ ((s : G) * conjUnipotent hMU k₂ u) *
            (1 + σ ((s : G) * conjUnipotent hMU k₂ u)) ^ (-d')) ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul A.coe_nonneg, hfun]
          exact ENNReal.ofReal_le_ofReal (hA k₁ hk₁ k₂ hk₂ _)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          hν.lintegral_comp k₂
            (fun u => ENNReal.ofReal (Ξ ((s : G) * u) *
              (1 + σ ((s : G) * u)) ^ (-d'))), hδK k₂ hk₂]
        simp
  have hR : ENNReal.ofReal (ΞM s * (1 + σM s) ^ (-d)) ≤
      (B : ℝ≥0∞) * ENNReal.ofReal
        (ΞM (k₁ * s * k₂) * (1 + σM (k₁ * s * k₂)) ^ (-d)) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul B.coe_nonneg]
    have hh := hB k₁⁻¹ (KM.inv_mem hk₁) k₂⁻¹ (KM.inv_mem hk₂) (k₁ * s * k₂)
    rw [show k₁⁻¹ * (k₁ * s * k₂) * k₂⁻¹ = s by group] at hh
    exact ENNReal.ofReal_le_ofReal hh
  let I : ℝ≥0∞ := ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
    (1 + σ ((s : G) * u)) ^ (-d')) ∂ν
  rw [hδ, ENNReal.coe_mul, ENNReal.coe_mul]
  calc (NNReal.sqrt (δ s) : ℝ≥0∞) * _ ≤
        (NNReal.sqrt (δ s) : ℝ≥0∞) * ((A : ℝ≥0∞) * I) :=
          mul_le_mul_right hint _
    _ = (A : ℝ≥0∞) * ((NNReal.sqrt (δ s) : ℝ≥0∞) * I) := by ring
    _ ≤ (A : ℝ≥0∞) * ((c : ℝ≥0∞) *
        ENNReal.ofReal (ΞM s * (1 + σM s) ^ (-d))) := by
          exact mul_le_mul_right (hc s hs) _
    _ ≤ (A : ℝ≥0∞) * ((c : ℝ≥0∞) * ((B : ℝ≥0∞) *
        ENNReal.ofReal (ΞM (k₁ * s * k₂) * (1 + σM (k₁ * s * k₂)) ^ (-d)))) :=
          mul_le_mul_right (mul_le_mul_right hR _) _
    _ = _ := by ring

end Cover

/-- The compact double-coset reduction with uniform bounds for the two kernels. -/
def ConstantTermCompactCoverStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (M U : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (ν : Measure U) (δ : M →* ℝ≥0ˣ) (Ξ σ : G → ℝ) (ΞM σM : M → ℝ)
    (KM : Subgroup M) (S : Set M),
    IsConjModulus hMU ν δ → (∀ k ∈ KM, δ k = 1) → IsDoubleCosetCover KM S →
    (∀ r : ℝ, ∃ A : ℝ≥0, ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g : G,
      Ξ ((k₁ : G) * g * k₂) * (1 + σ ((k₁ : G) * g * k₂)) ^ (-r) ≤
        A * (Ξ g * (1 + σ g) ^ (-r))) →
    (∀ r : ℝ, ∃ B : ℝ≥0, ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m : M,
      ΞM (k₁ * m * k₂) * (1 + σM (k₁ * m * k₂)) ^ (-r) ≤
        B * (ΞM m * (1 + σM m) ^ (-r))) →
    (∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ s ∈ S,
      (NNReal.sqrt (δ s) : ℝ≥0∞) *
          ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-d')) ∂ν ≤
        c * ENNReal.ofReal (ΞM s * (1 + σM s) ^ (-d))) →
    ConstantTermEstimate ν δ Ξ σ ΞM σM

/-- The compact reduction for arbitrary weights and arbitrary carrier universe. -/
theorem constantTermCompactCover : ConstantTermCompactCoverStatement.{u} := by
  intro G _ _ _ _ _ M U hMU ν δ Ξ σ ΞM σM KM S hν hδK hcover hGker hMker hS
  exact constantTermEstimate_of_doubleCosetCover hν hδK hcover hGker hMker hS

end Langlands.HarishChandraSchwartz
