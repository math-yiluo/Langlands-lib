import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalFactorIntegral

/-! # Rapid decay of the open-cell factor integral

The Levi Xi upper bound and a linear height cutoff turn the integrated
tail estimate into arbitrary polynomial decay with the desired modulus
weight.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Powers

variable {X : Type*} {Ξ σ η t eA e₀ : X → ℝ} {T : Set X}

/-- A linear cutoff absorbs the polynomial loss in a squared Xi upper
bound, leaving any prescribed negative power of the height. -/
theorem exists_cutoff_xi_sq_le
    (hΞ : ∀ x, 0 ≤ Ξ x) (hσ : ∀ x, 0 ≤ σ x) (hη : ∀ x, 0 ≤ η x)
    (hup : XiUpperBound Ξ σ T eA)
    (heA : ∀ x ∈ T, η x * eA x ^ 2 ≤ e₀ x ^ 2)
    (ht : ∃ b : ℝ, 0 < b ∧ ∀ x ∈ T, b * (1 + σ x) ≤ t x)
    (r : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ ∃ B : ℝ≥0, ∀ x ∈ T,
      η x * t x ^ (-p) * Ξ x ^ 2 ≤
        B * (e₀ x ^ 2 * (1 + σ x) ^ (-r)) := by
  obtain ⟨C, D, hupper⟩ := hup
  obtain ⟨b, hb, hcut⟩ := ht
  let p := max (r + 2 * D) 0
  have hp : 0 ≤ p := le_max_right _ _
  have hpr : r + 2 * D ≤ p := le_max_left _ _
  let B : ℝ := b ^ (-p) * C ^ 2
  have hB : 0 ≤ B := by positivity
  refine ⟨p, hp, Real.toNNReal B, fun x hx => ?_⟩
  rw [Real.coe_toNNReal B hB]
  have hs : 0 < 1 + σ x := by linarith [hσ x]
  have htpos : 0 < t x := lt_of_lt_of_le (mul_pos hb hs) (hcut x hx)
  have hpow : t x ^ (-p) ≤ b ^ (-p) * (1 + σ x) ^ (-p) := by
    rw [← Real.mul_rpow hb.le hs.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hb hs) (hcut x hx) (neg_nonpos.mpr hp)
  have hxisq : Ξ x ^ 2 ≤ C ^ 2 * eA x ^ 2 * (1 + σ x) ^ (2 * D) := by
    have h := pow_le_pow_left₀ (hΞ x) (hupper x hx) 2
    have hpowD : ((1 + σ x) ^ D) ^ 2 = (1 + σ x) ^ (2 * D) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      ring_nf
    calc
      Ξ x ^ 2 ≤ (C * eA x * (1 + σ x) ^ D) ^ 2 := h
      _ = C ^ 2 * eA x ^ 2 * ((1 + σ x) ^ D) ^ 2 := by ring
      _ = _ := by rw [hpowD]
  have hpowr :
      (1 + σ x) ^ (-p) * (1 + σ x) ^ (2 * D) ≤ (1 + σ x) ^ (-r) := by
    rw [← Real.rpow_add hs]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hσ x]) (by linarith)
  have hηx := hη x
  calc
    η x * t x ^ (-p) * Ξ x ^ 2 ≤
        η x * (b ^ (-p) * (1 + σ x) ^ (-p)) *
          (C ^ 2 * eA x ^ 2 * (1 + σ x) ^ (2 * D)) := by
      gcongr
    _ = B * (η x * eA x ^ 2) *
        ((1 + σ x) ^ (-p) * (1 + σ x) ^ (2 * D)) := by dsimp [B]; ring
    _ ≤ B * (e₀ x ^ 2) * (1 + σ x) ^ (-r) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (heA x hx) hB
      · exact hpowr
      · positivity
      · positivity
    _ = _ := by ring

end Powers

section Integral

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U V : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)}
  {νU : Measure U} {δU : M →* ℝ≥0ˣ} {νV : Measure V} {δV : M →* ℝ≥0ˣ}
  {ΞM σM : M → ℝ} {σ : G → ℝ} {KM : Subgroup M} [CompactSpace KM]
  [SecondCountableTopology M] {muM : Measure M} [SFinite muM]
  [muM.IsMulLeftInvariant] [muM.IsMulRightInvariant]

/-- The arbitrary-power decay conclusion for the product integral in the
cuspidal open-cell part. -/
def CuspidalFactorIntegralDecayBound
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (νU : Measure U) (δU : M →* ℝ≥0ˣ) (νV : Measure V) (δV : M →* ℝ≥0ˣ)
    (muM : Measure M) (Γ : Set U) (A : M → Set V) (f₁ f₂ : G → ℂ)
    (T : Set M) (e₀ : M → ℝ) (σ : G → ℝ) : Prop :=
  ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T,
    ∫⁻ m : M, ‖cuspidalFactor hMU νU δU Γ f₁ a (a * m * a⁻¹)‖ₑ *
        ‖unipotentFactor νV δV (A a) f₂ m‖ₑ ∂muM ≤
      c * ENNReal.ofReal (e₀ a ^ 2 * (1 + σ a) ^ (-r))

/-- The open-cell factor integral has rapid decay from the two factor
bounds, Levi convolution weights, its chamber Xi upper estimate and a
linear height cutoff. No exact invariance of the original ambient weights
or cutoff sets under a structural compact subgroup is a premise. -/
theorem cuspidalFactorIntegralDecayBound_of_tail
    (hwM : ConvolutionWeights muM KM ΞM σM)
    (hσr : ∀ k ∈ KM, ∀ m : M, σM (m * k) = σM m)
    {Γ : Set U} {A : M → Set V} {f₁ f₂ : G → ℂ}
    {T : Set M} {t eA e₀ : M → ℝ}
    (h₁ : CuspidalFactorTailBound hMU νU δU Γ f₁ T t ΞM σM)
    (h₂ : UnipotentFactorDecayBound νV δV A f₂ ΞM σM)
    (hσ : ∀ g, 0 ≤ σ g)
    (hup : XiUpperBound ΞM (fun m => σ m) T eA)
    (heA : ∀ a ∈ T, (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) * eA a ^ 2 ≤ e₀ a ^ 2)
    (ht : ∃ b : ℝ, 0 < b ∧ ∀ a ∈ T, b * (1 + σ a) ≤ t a) :
    CuspidalFactorIntegralDecayBound hMU νU δU νV δV muM Γ A f₁ f₂ T e₀ σ := by
  intro r
  obtain ⟨p, hp, B, hB⟩ := exists_cutoff_xi_sq_le
    (fun m => (hwM.pos m).le) (fun m => hσ m)
    (fun m => NNReal.coe_nonneg ((δU m : ℝ≥0)⁻¹)) hup heA ht r
  obtain ⟨c, hc⟩ := lintegral_cuspidalFactors_le_of_tail hwM hσr h₁ h₂ hp
  refine ⟨c * B, fun a ha => (hc a ha).trans ?_⟩
  have hδ : 0 ≤ (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  obtain ⟨b, hb, hcut⟩ := ht
  have hta : 0 < t a :=
    lt_of_lt_of_le (mul_pos hb (by linarith [hσ a])) (hcut a ha)
  calc
    (c : ℝ≥0∞) * (((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ENNReal.ofReal (t a ^ (-p)) * ENNReal.ofReal (ΞM a ^ 2) =
      c * ENNReal.ofReal
        ((((δU a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) * t a ^ (-p) * ΞM a ^ 2) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hδ (Real.rpow_nonneg hta.le _)),
        ENNReal.ofReal_mul hδ, ENNReal.ofReal_coe_nnreal]
      ring
    _ ≤ c * ENNReal.ofReal
        ((B : ℝ) * (e₀ a ^ 2 * (1 + σ a) ^ (-r))) :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hB a ha)) zero_le
    _ = _ := by
      rw [ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
      ring

end Integral

end Langlands.HarishChandraSchwartz
