import Langlands.Representation.Archimedean.RealBlockJacquet

/-!
# The limit along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)` in value form

Let `χ` be signed-power characters whose exponents satisfy `IsBlockDominant e a k` (tied on the
last `k+1` positions, strictly below the earlier ones), `u` in the principal series of `χ⁻¹` and
`h` in that of `χ` on `GL_{a+k+1}(ℝ)`. With `d(s) = diag(1_a, s·1_{k+1})`,

`∫_{O(a+k+1)} u(κ d(s)) h(κ) dκ`
`  = c · χ⁻¹δ^{1/2}(d(s)) · ∫_{O(a)} ∫_{O(k+1)} ∫_X u(n̄(s⁻¹X) m) h(n̄(X) m)`

with `m = diag(κ₁, κ₂)` and the constant `c > 0` of `RealBlockParabolicIntegrationStatement`
(`exists_integral_dTail_eq`), and along `s = m + 1` the triple integral tends to
`∫_{O(a)} ∫_{O(k+1)} u(m) T_P h(m)`, with `T_P h(g) = ∫_X h(n̄(X) g) dX` (`tendsto_Φ`). Hence the
normalized matrix coefficient converges (`exists_tendsto`). This is the value form of the limit
argument `RealBlockLimit.integral_mul_blockStep_eq_zero`, whose proof it follows.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealBlockLimitValue

open RealBlockParabolic RealBlockChart RealBlockLimit RealBlockJacquet PartialJacquet JacquetLimit
  RealPrincipalSeriesDuality MaximalParabolicIntegration

attribute [local instance] measurableSpaceK secondCountableTopology_unitaryCompact

local instance borelSpaceK_lv (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- The parameter `s_m = m + 1`, as a unit of `ℝ`. -/
def seqUnit (m : ℕ) : ℝˣ := Units.mk0 ((m : ℝ) + 1) (by positivity)

theorem seqUnit_val (m : ℕ) : ((seqUnit m : ℝˣ) : ℝ) = (m : ℝ) + 1 := rfl

variable (a k) in
/-- The normalizing factor `c'(s)`: the value of the character of the principal series of `χ⁻¹`
at `d(s) = diag(1_a, s·1_{k+1})`. -/
def tailFactor (χ : ℕ → ℝˣ → ℂ) (s : ℝˣ) : ℂ :=
  principalSeriesCharacter ℝ (a + (k + 1)) (dualChar χ) (tailEntries (a := a) (k := k + 1) s)

theorem tailFactor_ne_zero (hχ : IsSignedPower χ e) (s : ℝˣ) : tailFactor a k χ s ≠ 0 := by
  rw [tailFactor, ← norm_ne_zero_iff, norm_principalSeriesCharacter hχ.dual]
  exact (Finset.prod_pos fun l _ =>
    Real.rpow_pos_of_pos (abs_pos.mpr (Units.ne_zero _)) _).ne'

/-- The limit value `∫_{O(a)} ∫_{O(k+1)} u(diag(κ₁, κ₂)) T_P h(diag(κ₁, κ₂)) dκ₂ dκ₁`. -/
def limitValue (u h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) : ℂ :=
  ∫ κ₁ : unitaryCompact ℝ a, (∫ κ₂ : unitaryCompact ℝ (k + 1),
    u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ) (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) *
      blockStep h (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
        (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) ∂haarK (k + 1)) ∂haarK a

/-- **The integration identity.** There is `c > 0` (depending only on `a, k`) such that
`∫_{O(a+k+1)} u(κ d(s)) h(κ) dκ = c · c'(s) · ∫∫∫ Φ_s` for every `s > 0`. -/
theorem exists_integral_dTail_eq (hT3 : RealBlockParabolicIntegrationStatement) (a k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
      ∀ {u h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ},
      u ∈ principalSeries ℝ (a + (k + 1)) (dualChar χ) →
      h ∈ principalSeries ℝ (a + (k + 1)) χ →
      ∀ {s : ℝ} (hs : 0 < s),
        ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) * dTail (Units.mk0 s hs.ne')) * h κ
          ∂haarK (a + (k + 1)) =
        (c : ℂ) * tailFactor a k χ (Units.mk0 s hs.ne') *
          ∫ κ₁ : unitaryCompact ℝ a, (∫ κ₂ : unitaryCompact ℝ (k + 1),
            (∫ X : Fin (k + 1) → Fin a → ℝ, Φ u h s κ₁ κ₂ X) ∂haarK (k + 1)) ∂haarK a := by
  obtain ⟨c, hc, hT3'⟩ := hT3 a (k + 1)
  refine ⟨c, hc, ?_⟩
  intro χ e hχ u h hu hh s hs
  set s' : ℝˣ := Units.mk0 s hs.ne' with hs'
  set d : Langlands.GeneralLinear (a + (k + 1)) ℝ := dTail (a := a) (k := k + 1) s' with hd
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu d
  set F : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ := fun y => u (y * d) * h y with hFdef
  have hFs : ContMDiff (matrixModel ℝ (a + (k + 1))) 𝓘(ℝ, ℂ) ∞ F :=
    contMDiff_mul_fun hud.1 hh.1
  have hF : IsModulusCovariant F := by
    intro z v y
    simp only [hFdef]
    rw [mul_assoc _ y, hu.2 z v, hh.2 z v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  have h1 := (hT3' F hFs hF).2
  set c' := principalSeriesCharacter ℝ (a + (k + 1)) (dualChar χ) (tailEntries s') with hc'def
  have hdu : ∀ y, u (d * y) = c' * u y := fun y => by
    have := hu.2 (tailEntries s') 1 y
    simpa [hd, dTail] using this
  have hpt : ∀ (κ₁ : unitaryCompact ℝ a) (κ₂ : unitaryCompact ℝ (k + 1))
      (X : Fin (k + 1) → Fin a → ℝ),
      F (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ) (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) =
        c' * Φ u h s κ₁ κ₂ X := by
    intro κ₁ κ₂ X
    simp only [hFdef, Φ]
    rw [mul_assoc, blockDiagGL_mul_dTail, ← mul_assoc, blockLowerGL_mul_dTail, mul_assoc, hdu]
    have : ((s' : ℝ))⁻¹ • Matrix.of X = s⁻¹ • Matrix.of X := by
      rw [hs', Units.val_mk0]
    rw [this]
    ring
  simp_rw [hpt, integral_const_mul] at h1
  change ∫ κ, F (κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) ∂haarK (a + (k + 1)) = _
  rw [h1, tailFactor, ← hc'def]
  ring

/-- **The limit.** Along `s = m + 1`, `∫∫∫ Φ_s → ∫_{O(a)} ∫_{O(k+1)} u(m) T_P h(m)`. -/
theorem tendsto_Φ (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {u h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hu : u ∈ principalSeries ℝ (a + (k + 1)) (dualChar χ))
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) :
    Tendsto (fun m : ℕ => ∫ κ₁ : unitaryCompact ℝ a, (∫ κ₂ : unitaryCompact ℝ (k + 1),
      (∫ X, Φ u h ((m : ℝ) + 1) κ₁ κ₂ X) ∂haarK (k + 1)) ∂haarK a) atTop
      (𝓝 (limitValue u h)) := by
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  set γ : Fin a → ℝ := fun l => max (((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2) (-1) with hγ
  set D : (Fin (k + 1) → Fin a → ℝ) → ℝ := fun X => Cu * Ch * blockChartBound γ (Matrix.of X)
    with hD
  have hDi : Integrable D := (hT1 a (k + 1) γ (tail_max he.ord he.gap)).const_mul _
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hbound : ∀ (n : ℕ) (κ₁ : unitaryCompact ℝ a) (κ₂ : unitaryCompact ℝ (k + 1))
      (X : Fin (k + 1) → Fin a → ℝ), ‖Φ u h ((n : ℝ) + 1) κ₁ κ₂ X‖ ≤ D X :=
    fun n κ₁ κ₂ X => norm_Φ_le hχ he.tie hu hh hCu hCh (hn1 n) κ₁ κ₂ X
  -- the innermost limit
  have hX : ∀ (κ₁ : unitaryCompact ℝ a) (κ₂ : unitaryCompact ℝ (k + 1)),
      Tendsto (fun n : ℕ => ∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) atTop
        (𝓝 (u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) *
          ∫ X : Fin (k + 1) → Fin a → ℝ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))) := by
    intro κ₁ κ₂
    rw [← integral_const_mul]
    have hcX : ∀ n : ℕ, Continuous fun X : Fin (k + 1) → Fin a → ℝ =>
        Φ u h ((n : ℝ) + 1) κ₁ κ₂ X := fun n =>
      continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_const
        continuous_id
    refine tendsto_integral_of_dominated_convergence D
      (fun n => (hcX n).aestronglyMeasurable)
      hDi (fun n => ae_of_all _ (hbound n κ₁ κ₂)) (ae_of_all _ fun X => ?_)
    have hs : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ) • Matrix.of X) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) := by
        simpa [one_div] using h0
      simpa using h1.smul_const (Matrix.of X)
    have hcont : Continuous fun Y : Matrix (Fin (k + 1)) (Fin a) ℝ =>
        u (blockLowerGL (a := a) (k := k + 1) Y *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) :=
      hu.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)
    have h2 := (hcont.tendsto 0).comp hs
    simp only [Function.comp_def, blockLowerGL_zero, one_mul] at h2
    exact h2.mul_const _
  -- the middle limit
  have hK2 : ∀ κ₁ : unitaryCompact ℝ a,
      Tendsto (fun n : ℕ => ∫ κ₂ : unitaryCompact ℝ (k + 1),
        (∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) ∂haarK (k + 1)) atTop
        (𝓝 (∫ κ₂ : unitaryCompact ℝ (k + 1), u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) *
          (∫ X : Fin (k + 1) → Fin a → ℝ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℝ))) ∂haarK (k + 1))) := by
    intro κ₁
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ₂ => ?_) (ae_of_all _ fun κ₂ => hX κ₁ κ₂)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun q : unitaryCompact ℝ (k + 1) × (Fin (k + 1) → Fin a → ℝ) =>
          Φ u h ((n : ℝ) + 1) κ₁ q.1 q.2)
        (continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_fst
          continuous_snd).aestronglyMeasurable
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂))
  -- the outer limit
  refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
    (integrable_const _) (fun n => ae_of_all _ fun κ₁ => ?_) (ae_of_all _ hK2)
  · exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : unitaryCompact ℝ a × unitaryCompact ℝ (k + 1) =>
        ∫ X, Φ u h ((n : ℝ) + 1) p.1 p.2 X)
      (AEStronglyMeasurable.integral_prod_right'
        (f := fun p : (unitaryCompact ℝ a × unitaryCompact ℝ (k + 1)) ×
          (Fin (k + 1) → Fin a → ℝ) => Φ u h ((n : ℝ) + 1) p.1.1 p.1.2 p.2)
        (continuous_Φ hu.1.continuous hh.1.continuous _
          (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)
          continuous_snd).aestronglyMeasurable)
  · have := norm_integral_le_of_norm_le_const (μ := haarK (k + 1)) (C := ∫ X, D X)
      (ae_of_all _ fun κ₂ => norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂)))
    simpa using this

/-- **The limit in value form.** There is `c ≠ 0` (depending only on `a, k`) such that for all
`χ`, `u`, `h` as above, `(c · c'(s_m))⁻¹ ∫_{O(a+k+1)} u(κ d(s_m)) h(κ) dκ → limitValue u h` along
`s_m = m + 1`. -/
theorem exists_tendsto (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (a k : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
      IsBlockDominant e a k →
      ∀ {u h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ},
      u ∈ principalSeries ℝ (a + (k + 1)) (dualChar χ) →
      h ∈ principalSeries ℝ (a + (k + 1)) χ →
        Tendsto (fun m : ℕ => (c * tailFactor a k χ (seqUnit m))⁻¹ *
          ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) * dTail (seqUnit m)) * h κ
            ∂haarK (a + (k + 1))) atTop (𝓝 (limitValue u h)) := by
  obtain ⟨c, hc, hid⟩ := exists_integral_dTail_eq hT3 a k
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', ?_⟩
  intro χ e hχ he u h hu hh
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine (tendsto_Φ hT1 hχ he hu hh).congr fun m => ?_
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hseq : seqUnit m = Units.mk0 ((m : ℝ) + 1) hm.ne' := rfl
  rw [hseq, hid hχ hu hh hm, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hc0
    (tailFactor_ne_zero hχ _)), one_mul]

end RealBlockLimitValue

end Langlands.Archimedean
