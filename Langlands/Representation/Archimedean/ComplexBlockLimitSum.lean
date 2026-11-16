import Langlands.Representation.Archimedean.ComplexBlockLimit

/-!
# The limit argument along `P_{a,k+1}` for finite sums of matrix coefficients

`ComplexBlockLimit` shows: if `∫_{U(a+k+1)} u(κ g) h(κ) dκ = 0` for every `g`, then the leading term
`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁` vanishes. This file
proves the same for a finite family of pairs `(u_i, h_i)`: if
`∑_i ∫_{U(a+k+1)} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s ∈ ℂˣ`, where
`d(s) = diag(1_a, s·1_{k+1})`, then the sum of the leading terms vanishes. The hypothesis is needed
only along this ray. The case of two pairs is an identity between leading terms
(`ComplexBlockLimitSum.blockTerm_eq_of_integral_eq`). Both statements assume
`ComplexBlockChartIntegrableStatement` and `ComplexBlockParabolicIntegrationStatement`, like
`ComplexBlockLimit`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockLimitSum

open ComplexBlockParabolic ComplexBlockChart Langlands.GeneralLinear ComplexBlockLimit
open ComplexPartialJacquet ComplexJacquetLimit ComplexDuality ComplexKIntegralInvariance

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The triple integral `∫_{U(a)} ∫_{U(k+1)} ∫_X Φ_s(u, h)` of the limit argument. -/
def tripleΦ (u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (s : ℝ) : ℂ :=
  ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
    (∫ X : Fin (k + 1) → Fin a → ℂ, Φ u h s κ₁ κ₂ X) ∂unitaryHaar (k + 1)) ∂unitaryHaar a

/-- The leading term
`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`. -/
def blockTerm (u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) : ℂ :=
  ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
    u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
      (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))
    ∂unitaryHaar (k + 1)) ∂unitaryHaar a

/-- **The pairing identity for sums.** If `∑_i ∫_{U} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s`, then
`∑_i ∫∫∫ Φ_s(u_i, h_i) = 0` for every `s > 0`. -/
theorem sum_tripleΦ_eq_zero (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) {ι : Type*} (S : Finset ι)
    {u h : ι → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ∀ i ∈ S, u i ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : ∀ i ∈ S, h i ∈ principalSeries ℂ (a + (k + 1)) χ)
    (h0 : ∀ s : ℂˣ,
      ∑ i ∈ S, ∫ κ, u i ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        dTail (a := a) (k := k + 1) s) * h i κ ∂unitaryHaar (a + (k + 1)) = 0)
    {s : ℝ} (hs : 0 < s) :
    ∑ i ∈ S, tripleΦ (u i) (h i) s = 0 := by
  obtain ⟨c, hc, hT3'⟩ := hT3 a (k + 1)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set s' : ℂˣ := Units.mk0 (s : ℂ) hs0 with hs'
  set d : Langlands.GeneralLinear (a + (k + 1)) ℂ := dTail (a := a) (k := k + 1) s' with hd
  set c' := principalSeriesCharacter ℂ (a + (k + 1)) (dualChar χ) (tailEntries s') with hc'def
  have hterm : ∀ i ∈ S, ∫ κ, u i ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * d) * h i κ
      ∂unitaryHaar (a + (k + 1)) = (c : ℂ) * (c' * tripleΦ (u i) (h i) s) := by
    intro i hi
    have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) (hu i hi) d
    set F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ := fun y => u i (y * d) * h i y
      with hFdef
    have hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1))) := by
      refine ⟨contMDiff_mul_fun hud.1 (hh i hi).1, fun z v y => ?_⟩
      simp only [hFdef]
      rw [mul_assoc _ y, (hu i hi).2 z v, (hh i hi).2 z v y,
        ← principalSeriesCharacter_dual_mul hχ]
      ring
    have h1 := (hT3' F hF).2
    have hdu : ∀ y, u i (d * y) = c' * u i y := fun y => by
      have := (hu i hi).2 (tailEntries s') 1 y
      simpa [hd, dTail] using this
    have hpt : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1))
        (X : Fin (k + 1) → Fin a → ℂ),
        F (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) =
          c' * Φ (u i) (h i) s κ₁ κ₂ X := by
      intro κ₁ κ₂ X
      simp only [hFdef, Φ]
      rw [mul_assoc, blockDiagGL_mul_dTail, ← mul_assoc, blockLowerGL_mul_dTail, mul_assoc, hdu]
      have : ((s' : ℂ))⁻¹ • Matrix.of X = ((s⁻¹ : ℝ) : ℂ) • Matrix.of X := by
        rw [hs', Units.val_mk0, Complex.ofReal_inv]
      rw [this]
      ring
    simp_rw [hpt, integral_const_mul] at h1
    exact h1
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc'0 : c' ≠ 0 := by
    rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
    exact (Finset.prod_pos fun l _ =>
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero _)) _).ne'
  have h2 := h0 s'
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hc0
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hc'0
    · exact h4

/-- **The limit of the triple integrals.** Under the order hypotheses of `ComplexBlockLimit`,
`∫∫∫ Φ_{n+1}(u, h) → blockTerm u h` as `n → ∞` (dominated convergence; no vanishing hypothesis). -/
theorem tendsto_tripleΦ (hT1 : ComplexBlockChartIntegrableStatement)
    (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    (hord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re)
    (hgap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re)
    {u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) :
    Tendsto (fun n : ℕ => tripleΦ u h ((n : ℝ) + 1)) atTop (𝓝 (blockTerm u h)) := by
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  set γ : Fin a → ℝ := fun l => max ((e ((l : ℕ) + 1)).re - (e l).re - 1) (-2) with hγ
  set D : (Fin (k + 1) → Fin a → ℂ) → ℝ := fun X => Cu * Ch * blockChartBound γ (Matrix.of X)
    with hD
  have hDi : Integrable D := (hT1 a (k + 1) γ (tail_max hord hgap)).const_mul _
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hbound : ∀ (n : ℕ) (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1))
      (X : Fin (k + 1) → Fin a → ℂ), ‖Φ u h ((n : ℝ) + 1) κ₁ κ₂ X‖ ≤ D X :=
    fun n κ₁ κ₂ X => norm_Φ_le hχ htie hu hh hCu hCh (hn1 n) κ₁ κ₂ X
  -- the innermost limit
  have hX : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1)),
      Tendsto (fun n : ℕ => ∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) atTop
        (𝓝 (u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          ∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))) := by
    intro κ₁ κ₂
    rw [← integral_const_mul]
    have hcX : ∀ n : ℕ, Continuous fun X : Fin (k + 1) → Fin a → ℂ =>
        Φ u h ((n : ℝ) + 1) κ₁ κ₂ X := fun n =>
      continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_const
        continuous_id
    refine tendsto_integral_of_dominated_convergence D
      (fun n => (hcX n).aestronglyMeasurable)
      hDi (fun n => ae_of_all _ (hbound n κ₁ κ₂)) (ae_of_all _ fun X => ?_)
    have hs : Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) • Matrix.of X) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp h0
        simpa [Function.comp_def, one_div] using this
      simpa using h1.smul_const (Matrix.of X)
    have hcont : Continuous fun Y : Matrix (Fin (k + 1)) (Fin a) ℂ =>
        u (blockLowerGL (a := a) (k := k + 1) Y *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) :=
      hu.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)
    have h2 := (hcont.tendsto 0).comp hs
    simp only [Function.comp_def, blockLowerGL_zero, one_mul] at h2
    exact h2.mul_const _
  -- the middle limit
  have hK2 : ∀ κ₁ : unitaryCompact ℂ a,
      Tendsto (fun n : ℕ => ∫ κ₂ : unitaryCompact ℂ (k + 1),
        (∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) ∂unitaryHaar (k + 1)) atTop
        (𝓝 (∫ κ₂ : unitaryCompact ℂ (k + 1), u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) ∂unitaryHaar (k + 1))) := by
    intro κ₁
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ₂ => ?_) (ae_of_all _ fun κ₂ => hX κ₁ κ₂)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun q : unitaryCompact ℂ (k + 1) × (Fin (k + 1) → Fin a → ℂ) =>
          Φ u h ((n : ℝ) + 1) κ₁ q.1 q.2)
        (continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_fst
          continuous_snd).aestronglyMeasurable
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂))
  -- the outer limit
  refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
    (integrable_const _) (fun n => ae_of_all _ fun κ₁ => ?_) (ae_of_all _ hK2)
  · exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : unitaryCompact ℂ a × unitaryCompact ℂ (k + 1) =>
        ∫ X, Φ u h ((n : ℝ) + 1) p.1 p.2 X)
      (AEStronglyMeasurable.integral_prod_right'
        (f := fun p : (unitaryCompact ℂ a × unitaryCompact ℂ (k + 1)) ×
          (Fin (k + 1) → Fin a → ℂ) => Φ u h ((n : ℝ) + 1) p.1.1 p.1.2 p.2)
        (continuous_Φ hu.1.continuous hh.1.continuous _
          (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)
          continuous_snd).aestronglyMeasurable)
  · have := norm_integral_le_of_norm_le_const (μ := unitaryHaar (k + 1)) (C := ∫ X, D X)
      (ae_of_all _ fun κ₂ => norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂)))
    simpa using this

/-- **The limit argument along `P_{a,k+1}` for finite sums.** -/
theorem sum_blockTerm_eq_zero (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    (hord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re)
    (hgap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re)
    {ι : Type*} (S : Finset ι) {u h : ι → Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : ∀ i ∈ S, u i ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : ∀ i ∈ S, h i ∈ principalSeries ℂ (a + (k + 1)) χ)
    (h0 : ∀ s : ℂˣ,
      ∑ i ∈ S, ∫ κ, u i ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        dTail (a := a) (k := k + 1) s) * h i κ ∂unitaryHaar (a + (k + 1)) = 0) :
    ∑ i ∈ S, blockTerm (u i) (h i) = 0 := by
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ S, tripleΦ (u i) (h i) ((n : ℝ) + 1)) atTop
      (𝓝 (∑ i ∈ S, blockTerm (u i) (h i))) :=
    tendsto_finsetSum S fun i hi =>
      tendsto_tripleΦ hT1 hχ htie hord hgap (hu i hi) (hh i hi)
  have hzero : ∀ n : ℕ, ∑ i ∈ S, tripleΦ (u i) (h i) ((n : ℝ) + 1) = 0 := fun n =>
    sum_tripleΦ_eq_zero hT3 hχ S hu hh h0 (by positivity)
  simp only [hzero] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- **Identity form.** If two matrix-coefficient integrals agree along the ray `d(s)`, then so do
their leading terms. -/
theorem blockTerm_eq_of_integral_eq (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    (hord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re)
    (hgap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re)
    {u₁ h₁ u₂ h₂ : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu₁ : u₁ ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh₁ : h₁ ∈ principalSeries ℂ (a + (k + 1)) χ)
    (hu₂ : u₂ ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh₂ : h₂ ∈ principalSeries ℂ (a + (k + 1)) χ)
    (heq : ∀ s : ℂˣ,
      ∫ κ, u₁ ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * dTail (a := a) (k := k + 1) s) *
        h₁ κ ∂unitaryHaar (a + (k + 1)) =
      ∫ κ, u₂ ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * dTail (a := a) (k := k + 1) s) *
        h₂ κ ∂unitaryHaar (a + (k + 1))) :
    blockTerm u₁ h₁ = blockTerm u₂ h₂ := by
  have hneg : -u₂ ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ) :=
    (principalSeries ℂ (a + (k + 1)) (dualChar χ)).neg_mem hu₂
  have h := sum_blockTerm_eq_zero hT1 hT3 hχ htie hord hgap (Finset.univ : Finset Bool)
    (u := fun b => if b then u₁ else -u₂) (h := fun b => if b then h₁ else h₂)
    (fun b _ => by cases b <;> simpa) (fun b _ => by cases b <;> simpa) (fun s => by
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, Pi.neg_apply,
        neg_mul, integral_neg, heq s]
      ring)
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton] at h
  have hb : blockTerm (-u₂) h₂ = -blockTerm u₂ h₂ := by
    simp only [blockTerm, Pi.neg_apply, neg_mul, integral_neg]
  rw [hb] at h
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)

end ComplexBlockLimitSum

end Langlands.Archimedean
