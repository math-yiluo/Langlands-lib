import Langlands.Global.RankinSelberg.EisensteinPoissonSplit
import Langlands.Global.RankinSelberg.EqualAnalyticPoles
import Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated

/-! # Analytic properties of the mirabolic Eisenstein series -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands.Global
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Eisenstein

open EqualAnalytic

local instance proofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance proofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "n" => (r + 1)

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
variable {Φ Ψ : RowVector F (r + 1) → ℂ}

/-- The two positive-height Mellin tails in the Poisson decomposition. -/
private def entirePart (Φ Ψ : RowVector F n → ℂ) (g : Points F n) (s : ℂ) : ℂ :=
  positiveTail F r χ Φ g s + positiveTail F r χ⁻¹ Ψ (iota F n g) (1 - s)

private theorem entirePart_differentiable (hΦc : Continuous Φ) (hΦd : IsRowDominated F n Φ)
    (hΨc : Continuous Ψ) (hΨd : IsRowDominated F n Ψ) (g : Points F n) :
    Differentiable ℂ (entirePart F r χ Φ Ψ g) :=
  (positiveTail_differentiable F r χ hΦc hΦd g).add
    ((positiveTail_differentiable F r χ⁻¹ hΨc hΨd (iota F n g)).comp
      ((differentiable_const (c := (1 : ℂ))).sub differentiable_id))

private theorem exists_entirePart_bound (hΦd : IsRowDominated F n Φ)
    (hΨd : IsRowDominated F n Ψ) {K : Set (Points F n)} (hK : IsCompact K) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖entirePart F r χ Φ Ψ g s‖ ≤ C := by
  obtain ⟨C, hC₀, hC⟩ := exists_positiveTail_bound F r χ hΦd hK b
  obtain ⟨D, hD₀, hD⟩ := exists_positiveTail_bound F r χ⁻¹ hΨd
    (hK.image (UnequalAnalytic.continuous_iota F n)) (1 - a)
  refine ⟨C + D, add_nonneg hC₀ hD₀, fun g hg s ha hb => ?_⟩
  have hs : (1 - s).re ≤ 1 - a := by
    rw [Complex.sub_re, Complex.one_re]
    exact sub_le_sub_left ha 1
  exact (norm_add_le _ _).trans (add_le_add (hC g hg s hb) (hD _ ⟨g, hg, rfl⟩ _ hs))

private theorem entirePart_dual (g : Points F n) (s : ℂ) :
    entirePart F r χ Φ Ψ g s = entirePart F r χ⁻¹ Ψ Φ (iota F n g) (1 - s) := by
  simp only [entirePart, UnequalAnalytic.iota_iota, sub_sub_cancel]
  exact add_comm _ _

private theorem rightHalfPlane_exponents_pos {β : ℝ} {s : ℂ}
    (hs : 1 - β / ((n : ℕ) : ℝ) < s.re) :
    0 < β + ((n : ℕ) : ℝ) * s.re ∧ 0 < β + ((n : ℕ) : ℝ) * (s - 1).re := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by positivity
  have hd : -β / ((n : ℕ) : ℝ) < (s - 1).re := by
    rw [neg_div, Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hsub : (s - 1).re < s.re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h₁ := (div_lt_iff₀ hn).mp (hd.trans hsub)
  have h₂ := (div_lt_iff₀ hn).mp hd
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

/-- On a right half-plane the absolutely convergent series equals its Poisson decomposition. -/
private theorem exists_poisson_split (hP : IsThetaPoissonPair F r Φ Ψ)
    (hΦc : Continuous Φ) (hΦd : IsRowDominated F n Φ) :
    ∃ σ : ℝ, ∀ (g : Points F n) (s : ℂ), σ < s.re →
      Integrable (eisensteinSectionIntegrand F χ Φ s g) (ideleMeasure F) ∧
      Summable (fun q : LeftCosetSpace (eisensteinParabolic F r) =>
        ‖eisensteinSection F χ Φ s (rationalPoint F n q.out * g)‖) ∧
      eisensteinSeries F χ Φ s g = entirePart F r χ Φ Ψ g s +
        Ψ 0 * negativeBoundary F r χ g (s - 1) - Φ 0 * negativeBoundary F r χ g s := by
  obtain ⟨σ, hσ⟩ := exists_convergence_abscissa F r χ hΦc hΦd
  obtain ⟨β, C, _, hχ⟩ := exists_ideleChar_bound F χ
  refine ⟨max σ (1 - β / ((n : ℕ) : ℝ)), fun g s hs => ?_⟩
  obtain ⟨hM, hI, hS, hE⟩ := hσ g s ((le_max_left _ _).trans_lt hs)
  obtain ⟨ht, ht'⟩ := rightHalfPlane_exponents_pos r ((le_max_right _ _).trans_lt hs)
  exact ⟨hI, hS, hE.trans (integral_mellin_eq F r χ hP g s hM
    (negativeBoundary_integrable F r χ g s hχ ht)
    (negativeBoundary_integrable F r χ g (s - 1) hχ ht'))⟩

/-- The factor common to both boundary numerators for a norm power. -/
private def boundaryFactor (w : ℂ) (g : Points F n) : ℂ :=
  Complex.exp (-(w / (r + 1 : ℂ)) * (Real.log (detNorm F n g) : ℂ))

private def normPowerContinuation (Φ Ψ : RowVector F n → ℂ) (w : ℂ)
    (g : Points F n) (s : ℂ) : ℂ :=
  entirePart F r χ Φ Ψ g s +
    (boundaryFactor F r w g * Ψ 0) / (((n : ℕ) : ℂ) * s + (w - ((n : ℕ) : ℂ))) +
    (-(boundaryFactor F r w g * Φ 0)) / (((n : ℕ) : ℂ) * s + w)

private theorem poissonBoundary_eq_normPower {w : ℂ}
    (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) (g : Points F n) (s : ℂ)
    (hs : 1 - w.re / ((n : ℕ) : ℝ) < s.re) :
    entirePart F r χ Φ Ψ g s + Ψ 0 * negativeBoundary F r χ g (s - 1) -
      Φ 0 * negativeBoundary F r χ g s = normPowerContinuation F r χ Φ Ψ w g s := by
  obtain ⟨ht, ht'⟩ := rightHalfPlane_exponents_pos r hs
  have hre (t : ℂ) : (w + ((n : ℕ) : ℂ) * t).re = w.re + ((n : ℕ) : ℝ) * t.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero]
  have hden : w + ((n : ℕ) : ℂ) * (s - 1) =
      ((n : ℕ) : ℂ) * s + (w - ((n : ℕ) : ℂ)) := by ring
  rw [negativeBoundary_eq_of_char F r χ hw g (s - 1) (by rwa [hre]),
    negativeBoundary_eq_of_char F r χ hw g s (by rwa [hre]), hden,
    add_comm w (((n : ℕ) : ℂ) * s), normPowerContinuation, boundaryFactor]
  ring

private theorem normPower_poles {w : ℂ} (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) :
    -(w - ((n : ℕ) : ℂ)) / ((n : ℕ) : ℂ) ∈ equalPoleSet F n χ ∧
      -w / ((n : ℕ) : ℂ) ∈ equalPoleSet F n χ := by
  have hn : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
  refine ⟨⟨w, hw, Or.inr ?_⟩, ⟨w, hw, Or.inl rfl⟩⟩
  rw [neg_sub, sub_div, div_self hn]

private theorem normPowerContinuation_poles {w : ℂ}
    (hw : ∀ z, ideleChar F χ z = detPower F 1 z w) (g : Points F n)
    (hT : Differentiable ℂ (entirePart F r χ Φ Ψ g)) :
    HasAtMostSimplePolesIn (normPowerContinuation F r χ Φ Ψ w g) (equalPoleSet F n χ) := by
  have hn : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
  obtain ⟨h₁, h₂⟩ := normPower_poles F r χ hw
  exact hasAtMostSimplePolesIn_two hT hn h₁ h₂

private theorem exists_normPowerContinuation_bound {w : ℂ}
    (hw : ∀ z, ideleChar F χ z = detPower F 1 z w)
    (hΦd : IsRowDominated F n Φ) (hΨd : IsRowDominated F n Ψ)
    {K : Set (Points F n)} (hK : IsCompact K) (a b : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      (∀ p ∈ equalPoleSet F n χ, δ ≤ ‖s - p‖) →
      ‖normPowerContinuation F r χ Φ Ψ w g s‖ ≤ C := by
  obtain ⟨T, hT₀, hT⟩ := exists_entirePart_bound F r χ hΦd hΨd hK a b
  have hlog : Continuous (fun g : Points F n => Real.log (detNorm F n g)) := by
    refine continuous_iff_continuousAt.mpr fun g => ?_
    exact (Real.continuousAt_log (UnequalAnalytic.detNorm_pos F g).ne').comp
      (UnequalAnalytic.continuous_detNorm F n).continuousAt
  have hf : Continuous (boundaryFactor F r w) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hB₀ : 0 ≤ max B 0 := le_max_right _ _
  let bound (v : ℂ) := (max B 0 * ‖v‖ / ‖((n : ℕ) : ℂ)‖) / δ
  have hbound (v : ℂ) : 0 ≤ bound v := by
    dsimp [bound]
    positivity
  refine ⟨T + bound (Ψ 0) + bound (Φ 0),
    add_nonneg (add_nonneg hT₀ (hbound _)) (hbound _), fun g hg s ha hb hpole => ?_⟩
  have hn : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
  have hfrac (v d : ℂ) (hp : -d / ((n : ℕ) : ℂ) ∈ equalPoleSet F n χ) :
      ‖boundaryFactor F r w g * v / (((n : ℕ) : ℂ) * s + d)‖ ≤ bound v := by
    rw [frac_eq _ _ _ _ hn, norm_div, norm_div, norm_mul]
    calc
      _ ≤ (‖boundaryFactor F r w g‖ * ‖v‖ / ‖((n : ℕ) : ℂ)‖) / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ (hpole _ hp)
      _ ≤ bound v := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((hB g hg).trans (le_max_left _ _)) (norm_nonneg _))
          (norm_nonneg _)) hδ.le
  obtain ⟨h₁, h₂⟩ := normPower_poles F r χ hw
  unfold normPowerContinuation
  refine norm_add₃_le.trans ?_
  rw [neg_div, norm_neg]
  exact add_le_add (add_le_add (hT g hg s ha hb) (hfrac _ _ h₁)) (hfrac _ _ h₂)

private theorem normPowerContinuation_dual (w : ℂ) (g : Points F n) (s : ℂ) :
    normPowerContinuation F r χ Φ Ψ w g s =
      normPowerContinuation F r χ⁻¹ Ψ Φ (-w) (iota F n g) (1 - s) := by
  have hf : boundaryFactor F r (-w) (iota F n g) = boundaryFactor F r w g := by
    simp only [boundaryFactor, log_detNorm_iota, Complex.ofReal_neg, neg_div, neg_neg,
      mul_neg, neg_mul]
  have h₁ : ((n : ℕ) : ℂ) * (1 - s) + (-w - ((n : ℕ) : ℂ)) =
      -(((n : ℕ) : ℂ) * s + w) := by ring
  have h₂ : ((n : ℕ) : ℂ) * (1 - s) + -w =
      -(((n : ℕ) : ℂ) * s + (w - ((n : ℕ) : ℂ))) := by ring
  simp only [normPowerContinuation]
  rw [← entirePart_dual F r χ g s, hf, h₁, h₂]
  simp only [div_neg_eq_neg_div, neg_div, neg_neg]
  ring

end

/-- Cogdell 2004, §2.3: convergence, continuation, strip bounds and the functional equation. -/
theorem eisenstein : EisensteinStatement.{u} := by
  intro F _ _ _ r ψ hψ χ Φ hΦ
  let n := r + 1
  let Ψ := fourierTransform F n ψ Φ
  obtain ⟨hΦc, _, hΦd⟩ := schwartzBruhat_properties F n hΦ
  obtain ⟨hΨc, hΨd⟩ := fourierTransform_properties F n ψ hψ hΦ
  have hP : IsThetaPoissonPair F r Φ Ψ := isThetaPoissonPair_fourier F r ψ hψ hΦ
  obtain ⟨σ, hσ⟩ := exists_poisson_split F r χ hP hΦc hΦd
  obtain ⟨τ, hτ⟩ := exists_poisson_split F r χ⁻¹ (IsThetaPoissonPair.symm F r hP) hΨc hΨd
  have hT := entirePart_differentiable F r χ hΦc hΦd hΨc hΨd
  have hT' := entirePart_differentiable F r χ⁻¹ hΨc hΨd hΦc hΦd
  rcases ideleChar_dichotomy F χ with ⟨w, hw⟩ | ⟨z, hz, hχ⟩
  · have hw' (z : Points F 1) : ideleChar F χ⁻¹ z = detPower F 1 z (-w) := by
      rw [ideleChar_inv, hw, detPower_one_eq, detPower_one_eq, neg_mul, Complex.exp_neg]
    let a := 1 - w.re / ((n : ℕ) : ℝ)
    let b := 1 - (-w).re / ((n : ℕ) : ℝ)
    refine ⟨max (max σ τ) (max a b), normPowerContinuation F r χ Φ Ψ w,
      normPowerContinuation F r χ⁻¹ Ψ Φ (-w), ?_, ?_, ?_, ?_⟩
    · intro g s hs
      have hc := (le_max_left (max σ τ) (max a b)).trans_lt hs
      have hp := (le_max_right (max σ τ) (max a b)).trans_lt hs
      obtain ⟨hI, hS, hE⟩ := hσ g s ((le_max_left σ τ).trans_lt hc)
      obtain ⟨hI', hS', hE'⟩ := hτ g s ((le_max_right σ τ).trans_lt hc)
      exact ⟨hI, hI', hS, hS',
        (hE.trans (poissonBoundary_eq_normPower F r χ hw g s
          ((le_max_left a b).trans_lt hp))).symm,
        (hE'.trans (poissonBoundary_eq_normPower F r χ⁻¹ hw' g s
          ((le_max_right a b).trans_lt hp))).symm⟩
    · intro g
      exact ⟨normPowerContinuation_poles F r χ hw g (hT g),
        normPowerContinuation_poles F r χ⁻¹ hw' g (hT' g)⟩
    · intro K hK a b _ δ hδ
      exact exists_normPowerContinuation_bound F r χ hw hΦd hΨd hK a b δ hδ
    · intro g s _
      exact normPowerContinuation_dual F r χ w g s
  · have hχ' : ideleChar F χ⁻¹ z ≠ 1 := by
      rw [ideleChar_inv]
      intro h
      apply hχ
      simpa only [inv_inv, inv_one] using congrArg (fun x : ℂ => x⁻¹) h
    refine ⟨max σ τ, entirePart F r χ Φ Ψ, entirePart F r χ⁻¹ Ψ Φ, ?_, ?_, ?_, ?_⟩
    · intro g s hs
      obtain ⟨hI, hS, hE⟩ := hσ g s ((le_max_left σ τ).trans_lt hs)
      obtain ⟨hI', hS', hE'⟩ := hτ g s ((le_max_right σ τ).trans_lt hs)
      simp only [negativeBoundary_eq_zero F r χ hz hχ, mul_zero, add_zero, sub_zero] at hE
      simp only [negativeBoundary_eq_zero F r χ⁻¹ hz hχ', mul_zero, add_zero, sub_zero] at hE'
      exact ⟨hI, hI', hS, hS', hE.symm, hE'.symm⟩
    · intro g
      exact ⟨hasAtMostSimplePolesIn_entire (hT g) _, hasAtMostSimplePolesIn_entire (hT' g) _⟩
    · intro K hK a b _ δ _
      obtain ⟨C, hC₀, hC⟩ := exists_entirePart_bound F r χ hΦd hΨd hK a b
      exact ⟨C, hC₀, fun g hg s ha hb _ => hC g hg s ha hb⟩
    · intro g s _
      exact entirePart_dual F r χ g s

end Langlands.Global.RankinSelbergGlobal.Eisenstein
