import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConjugationBound

/-! # The cuspidal part of the proof of Proposition VIII.3.1

Waldspurger 2003, proof of Proposition VIII.3.1 (printed pp. 324–326): the estimates (4),
(5) and (6) for the integral `J(a)` over `a⁻¹ Γ a M Γ̄`, and the final assembly.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Tail

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM : M → ℝ} {KM : Subgroup M}

/-- Inequality (6) of the proof of Proposition VIII.3.1, for abstract data: the estimate of
Proposition II.4.5 restricted to a subset `V ⊆ U` on which `1 + σ ≥ t`, with an extra
factor `t^{-d''}`. The constants do not depend on `V` and `t`; `V` must be invariant under
conjugation by `K_M`. The hypotheses are those of `constantTermEstimate_of_bounds`. -/
theorem setLIntegral_estimate_of_bounds {S : Set M} {e eM : M → ℝ} {w : U → ℝ}
    (hν : IsConjModulus hMU ν δ) (hδK : ∀ k ∈ KM, δ k = 1)
    (hcover : IsDoubleCosetCover KM S)
    (hΞK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, Ξ ((k₁ : G) * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, σ ((k₁ : G) * g * k₂) = σ g)
    (hΞMK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m, ΞM (k₁ * m * k₂) = ΞM m)
    (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 ≤ ΞM m) (he : ∀ m ∈ S, 0 ≤ e m)
    (hw : ∀ u, 0 ≤ w u) (heM : ∀ m ∈ S, e m * NNReal.sqrt (δ m) ≤ eM m)
    (h44 : UnipotentXiBound Ξ σ S e w) (h31 : SigmaProductBound M U σ)
    (h11 : XiLowerBound ΞM S eM) (h42 : UnipotentWeightIntegrable ν w σ)
    (d : ℝ) {d'' : ℝ} (hd'' : 0 ≤ d'') :
    ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ (V : Set U) (t : ℝ), 0 < t → (∀ u ∈ V, t ≤ 1 + σ u) →
      (∀ k ∈ KM, ∀ u, conjUnipotent hMU k u ∈ V ↔ u ∈ V) → ∀ m : M,
        (NNReal.sqrt (δ m) : ℝ≥0∞) * ∫⁻ u, V.indicator (fun u : U =>
          ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d'))) u ∂ν ≤
        c * ENNReal.ofReal (t ^ (-d'')) * ENNReal.ofReal (ΞM m * (1 + σ m) ^ (-d)) := by
  obtain ⟨D, c₁, h44⟩ := h44
  obtain ⟨C₂, hC₂, h31⟩ := h31
  obtain ⟨C₃, h11⟩ := h11
  obtain ⟨d₂, hI₂⟩ := h42
  set r := max (max d (d₂ + d'')) 0 with hr_def
  have hr : 0 ≤ r := le_max_right _ _
  have hdr : d ≤ r := (le_max_left _ _).trans (le_max_left _ _)
  have hd₂r : d₂ + d'' ≤ r := (le_max_right _ _).trans (le_max_left _ _)
  set c₁' := max c₁ 0
  set C₃' := max C₃ 0
  set K : ℝ := c₁' * C₂ ^ (-(2 * r)) * C₃'
  have hK : 0 ≤ K := by positivity
  set I : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal (w u * (1 + σ u) ^ (-d₂)) ∂ν
  have hI : I ≠ ⊤ := hI₂.ne
  refine ⟨D + 2 * r, (Real.toNNReal K) * I.toNNReal, fun V t ht hVt hVK m => ?_⟩
  -- the bound at the points of `S`
  have key : ∀ s ∈ S, (NNReal.sqrt (δ s) : ℝ≥0∞) *
      ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal (Ξ ((s : G) * u) *
        (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))) u ∂ν ≤
      ENNReal.ofReal K * I * ENNReal.ofReal (t ^ (-d'')) *
        ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
    intro s hs
    set A : ℝ := c₁' * C₂ ^ (-(2 * r)) * e s * (1 + σ s) ^ (-r)
    have hA : 0 ≤ A := by
      have := he s hs
      have := hσ s
      positivity
    have htd : 0 ≤ t ^ (-d'') := Real.rpow_nonneg ht.le _
    have hpt : ∀ u : U, u ∈ V → Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) ≤
        A * t ^ (-d'') * (w u * (1 + σ u) ^ (-d₂)) := by
      intro u hu
      have hts : 0 < 1 + σ ((s : G) * u) := by linarith [hσ ((s : G) * u)]
      have hu1 : 1 ≤ 1 + σ u := by linarith [hσ u]
      have h1 : Ξ ((s : G) * u) ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ D := by
        refine (h44 s hs u).trans ?_
        have := he s hs
        have := hw u
        gcongr
        exact le_max_left _ _
      have h2 : Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) ≤
          c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := by
        calc Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))
            ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ D *
                (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := by
              rw [mul_assoc, ← Real.rpow_add hts]
              ring_nf
      have h3 := one_add_rpow_neg_le (hσ s) (hσ u) hC₂ hr (h31 s u)
      have h4 : (1 + σ u) ^ (-r) ≤ t ^ (-d'') * (1 + σ u) ^ (-d₂) := by
        calc (1 + σ u) ^ (-r) ≤ (1 + σ u) ^ (-(d'' + d₂)) :=
              Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
          _ = (1 + σ u) ^ (-d'') * (1 + σ u) ^ (-d₂) := by
              rw [neg_add, Real.rpow_add (by linarith)]
          _ ≤ t ^ (-d'') * (1 + σ u) ^ (-d₂) := by
              have : 0 ≤ (1 + σ u) ^ (-d₂) := Real.rpow_nonneg (by linarith) _
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_nonpos ht (hVt u hu) (by linarith)) this
      calc Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))
          ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := h2
        _ ≤ c₁' * e s * w u * (C₂ ^ (-(2 * r)) * ((1 + σ s) ^ (-r) * (1 + σ u) ^ (-r))) := by
            have := he s hs
            have := hw u
            gcongr
        _ = A * (w u * (1 + σ u) ^ (-r)) := by ring
        _ ≤ A * (w u * (t ^ (-d'') * (1 + σ u) ^ (-d₂))) := by
            have := hw u
            gcongr
        _ = A * t ^ (-d'') * (w u * (1 + σ u) ^ (-d₂)) := by ring
    have hint : ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal (Ξ ((s : G) * u) *
        (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))) u ∂ν ≤
        ENNReal.ofReal (A * t ^ (-d'')) * I := by
      calc ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))) u ∂ν
          ≤ ∫⁻ u, ENNReal.ofReal (A * t ^ (-d'')) *
              ENNReal.ofReal (w u * (1 + σ u) ^ (-d₂)) ∂ν := by
            refine lintegral_mono fun u => ?_
            by_cases hu : u ∈ V
            · rw [Set.indicator_of_mem hu, ← ENNReal.ofReal_mul (mul_nonneg hA htd)]
              exact ENNReal.ofReal_le_ofReal (hpt u hu)
            · rw [Set.indicator_of_notMem hu]
              exact zero_le
        _ = ENNReal.ofReal (A * t ^ (-d'')) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsq : (NNReal.sqrt (δ s) : ℝ) * A ≤ K * (ΞM s * (1 + σ s) ^ (-d)) := by
      have hσs := hσ s
      have h1 : (NNReal.sqrt (δ s) : ℝ) * A =
          c₁' * C₂ ^ (-(2 * r)) * (e s * NNReal.sqrt (δ s)) * (1 + σ s) ^ (-r) := by ring
      have h2 : e s * NNReal.sqrt (δ s) ≤ C₃' * ΞM s :=
        (heM s hs).trans ((h11 s hs).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞM s)))
      have h3 : (1 + σ s) ^ (-r) ≤ (1 + σ s) ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [h1]
      calc c₁' * C₂ ^ (-(2 * r)) * (e s * NNReal.sqrt (δ s)) * (1 + σ s) ^ (-r)
          ≤ c₁' * C₂ ^ (-(2 * r)) * (C₃' * ΞM s) * (1 + σ s) ^ (-d) := by
            have := hΞM s
            have : 0 ≤ e s * NNReal.sqrt (δ s) := mul_nonneg (he s hs) (NNReal.coe_nonneg _)
            gcongr
        _ = K * (ΞM s * (1 + σ s) ^ (-d)) := by ring
    calc (NNReal.sqrt (δ s) : ℝ≥0∞) *
          ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))) u ∂ν
        ≤ (NNReal.sqrt (δ s) : ℝ≥0∞) * (ENNReal.ofReal (A * t ^ (-d'')) * I) := by gcongr
      _ = ENNReal.ofReal ((NNReal.sqrt (δ s) : ℝ) * A) * I * ENNReal.ofReal (t ^ (-d'')) := by
          rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
            ENNReal.ofReal_coe_nnreal]
          ring
      _ ≤ ENNReal.ofReal (K * (ΞM s * (1 + σ s) ^ (-d))) * I *
            ENNReal.ofReal (t ^ (-d'')) := by
          gcongr
      _ = ENNReal.ofReal K * I * ENNReal.ofReal (t ^ (-d'')) *
            ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
          rw [ENNReal.ofReal_mul hK]
          ring
  -- reduction to `S` by the bi-invariance under `K_M`
  obtain ⟨k₁, hk₁, s, hs, k₂, hk₂, rfl⟩ := hcover m
  have hδ : δ (k₁ * s * k₂) = δ s := by
    rw [map_mul, map_mul, hδK k₁ hk₁, hδK k₂ hk₂, one_mul, mul_one]
  have hfun : ∀ u : U, (((k₁ * s * k₂ : M) : G) * u) =
      (k₁ : G) * ((s : G) * (conjUnipotent hMU k₂ u)) * (k₂ : G) := by
    intro u
    simp only [conjUnipotent, Subgroup.coe_mul]
    group
  set F : U → ℝ≥0∞ := V.indicator (fun u : U => ENNReal.ofReal (Ξ ((s : G) * u) *
    (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))) with hF
  have hind : ∀ u : U, V.indicator (fun u : U => ENNReal.ofReal
      (Ξ (((k₁ * s * k₂ : M) : G) * u) *
        (1 + σ (((k₁ * s * k₂ : M) : G) * u)) ^ (-(D + 2 * r)))) u =
      F (conjUnipotent hMU k₂ u) := by
    intro u
    simp only [hF]
    by_cases hu : u ∈ V
    · have hu' : conjUnipotent hMU k₂ u ∈ V := (hVK k₂ hk₂ u).mpr hu
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu', hfun, hΞK k₁ hk₁ k₂ hk₂,
        hσK k₁ hk₁ k₂ hk₂]
    · have hu' : conjUnipotent hMU k₂ u ∉ V := fun h => hu ((hVK k₂ hk₂ u).mp h)
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
  have hint : ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal
      (Ξ (((k₁ * s * k₂ : M) : G) * u) *
        (1 + σ (((k₁ * s * k₂ : M) : G) * u)) ^ (-(D + 2 * r)))) u ∂ν = ∫⁻ u, F u ∂ν := by
    simp only [hind]
    rw [hν.lintegral_comp k₂ F, hδK k₂ hk₂]
    simp
  have hRHS : ΞM (k₁ * s * k₂) * (1 + σ ((k₁ * s * k₂ : M) : G)) ^ (-d) =
      ΞM s * (1 + σ s) ^ (-d) := by
    rw [hΞMK k₁ hk₁ k₂ hk₂, Subgroup.coe_mul, Subgroup.coe_mul, hσK k₁ hk₁ k₂ hk₂]
  rw [hδ, hint, hRHS, ENNReal.coe_mul, ENNReal.coe_toNNReal hI]
  have := key s hs
  calc (NNReal.sqrt (δ s) : ℝ≥0∞) * ∫⁻ u, F u ∂ν
      ≤ ENNReal.ofReal K * I * ENNReal.ofReal (t ^ (-d'')) *
        ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := this
    _ = (Real.toNNReal K : ℝ≥0∞) * I * ENNReal.ofReal (t ^ (-d'')) *
        ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := rfl

end Tail

section Phi

theorem enorm_nnreal_mul (s : ℝ≥0) (z : ℂ) :
    ‖((s : ℝ) : ℂ) * z‖ₑ = (s : ℝ≥0∞) * ‖z‖ₑ := by
  rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]

/-- Cancellation: if `∫ f = 0`, then `|∫_B f| ≤ ∫_{V} |f|` for every `V ⊇ Bᶜ`. -/
theorem enorm_setIntegral_le_of_integral_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) (h0 : ∫ x, f x ∂μ = 0) {B V : Set α}
    (hB : MeasurableSet B) (hV : Bᶜ ⊆ V) :
    ‖∫ x in B, f x ∂μ‖ₑ ≤ ∫⁻ x, V.indicator (fun x => ‖f x‖ₑ) x ∂μ := by
  have h := integral_add_compl hB hf
  rw [h0, add_eq_zero_iff_eq_neg] at h
  rw [h, enorm_neg]
  calc ‖∫ x in Bᶜ, f x ∂μ‖ₑ ≤ ∫⁻ x in Bᶜ, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, Bᶜ.indicator (fun x => ‖f x‖ₑ) x ∂μ := (lintegral_indicator hB.compl _).symm
    _ ≤ ∫⁻ x, V.indicator (fun x => ‖f x‖ₑ) x ∂μ :=
        lintegral_mono fun x => Set.indicator_le_indicator_of_subset hV (fun _ => zero_le) x

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}

/-- `∫_U φ(u m) dν(u) = δ(m) ∫_U φ(m u) dν(u)`, from the modulus relation. -/
theorem IsConjModulus.lintegral_mul_right (hν : IsConjModulus hMU ν δ) (φ : G → ℝ≥0∞)
    (m : M) : ∫⁻ u : U, φ ((u : G) * m) ∂ν =
      ((δ m : ℝ≥0) : ℝ≥0∞) * ∫⁻ u : U, φ ((m : G) * u) ∂ν := by
  have h := hν.lintegral_comp m⁻¹ (fun u : U => φ ((m : G) * u))
  have hfun : ∀ u : U, (m : G) * (conjUnipotent hMU m⁻¹ u : G) = (u : G) * m := by
    intro u
    simp only [conjUnipotent, InvMemClass.coe_inv, inv_inv]
    group
  simp only [hfun] at h
  rw [h, map_inv, Units.val_inv_eq_inv_val, inv_inv]

/-- Inequality (4) of the proof of Proposition VIII.3.1, for abstract data: from the
estimate of Proposition II.4.5 for `(M, U)` (`ConstantTermEstimate`) and the modulus
relation, `δ(m)^{-1/2} ∫_U |f(u m)| du ≤ c ν_{d'}(f) Ξ^M(m) (1 + σ^M(m))^{-d}`. -/
theorem ConstantTermEstimate.lintegral_mul_right_le (hν : IsConjModulus hMU ν δ)
    {Ξ σ : G → ℝ} {ΞM σM : M → ℝ} (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (d : ℝ) :
    ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ f : G → ℂ, nu Ξ σ d' f ≠ ⊤ → ∀ m : M,
      (((NNReal.sqrt (δ m))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ u : U, ‖f ((u : G) * m)‖ₑ ∂ν ≤
        c * nu Ξ σ d' f * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d)) := by
  obtain ⟨d', c, hc⟩ := h d
  refine ⟨d', c, fun f hf m => ?_⟩
  set s := NNReal.sqrt (δ m : ℝ≥0)
  have hs : s ≠ 0 := by simp [s]
  have hδs : (δ m : ℝ≥0) = s * s := (NNReal.mul_self_sqrt _).symm
  rw [hν.lintegral_mul_right (fun g => ‖f g‖ₑ) m, hδs, ← mul_assoc, ← ENNReal.coe_mul,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  calc (s : ℝ≥0∞) * ∫⁻ u : U, ‖f ((m : G) * u)‖ₑ ∂ν
      ≤ (s : ℝ≥0∞) * ∫⁻ u : U, nu Ξ σ d' f *
          ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν := by
        gcongr with u
        exact enorm_le_nu_mul hΞ hσ f d' _
    _ = nu Ξ σ d' f * ((s : ℝ≥0∞) * ∫⁻ u : U,
          ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν) := by
        rw [lintegral_const_mul' _ _ hf]
        ring
    _ ≤ nu Ξ σ d' f * (c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) :=
        mul_le_mul_of_nonneg_left (hc m) zero_le
    _ = c * nu Ξ σ d' f * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d)) := by ring

/-- Inequality (5) of the proof of Proposition VIII.3.1, for abstract data: if
`∫_U f(m v) dν(v) = 0` (cuspidality, `f^{(P̄)} = 0`) and `Bᶜ ⊆ V` with
`B = a Γ̄ a⁻¹`, then `|∫_{Γ̄} f(m a ū a⁻¹) dū| ≤ δ(a)⁻¹ ∫_V |f(m v)| dv`. -/
theorem IsConjModulus.enorm_integral_conj_le (hν : IsConjModulus hMU ν δ) (a m : M)
    {f : G → ℂ} (hf : Integrable (fun v : U => f ((m : G) * v)) ν)
    (h0 : ∫ v : U, f ((m : G) * v) ∂ν = 0) {Γ V : Set U} (hΓ : MeasurableSet Γ)
    (hV : (conjUnipotent hMU a⁻¹ ⁻¹' Γ)ᶜ ⊆ V) :
    ‖∫ u : U, Γ.indicator (fun u => f ((m : G) * conjUnipotent hMU a u)) u ∂ν‖ₑ ≤
      (((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ v : U, V.indicator (fun v => ‖f ((m : G) * v)‖ₑ) v ∂ν := by
  set B := conjUnipotent hMU a⁻¹ ⁻¹' Γ
  have hB : MeasurableSet B :=
    (continuous_conjUnipotent hMU a⁻¹).measurable hΓ
  have hfun : (fun u => Γ.indicator (fun u => f ((m : G) * conjUnipotent hMU a u)) u) =
      fun u => B.indicator (fun v => f ((m : G) * v)) (conjUnipotent hMU a u) := by
    funext u
    have hinv : conjUnipotent hMU a⁻¹ (conjUnipotent hMU a u) = u :=
      (conjUnipotentHomeomorph hMU a).symm_apply_apply u
    by_cases hu : u ∈ Γ
    · have hu' : conjUnipotent hMU a u ∈ B := by
        show conjUnipotent hMU a⁻¹ (conjUnipotent hMU a u) ∈ Γ
        rw [hinv]
        exact hu
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu']
    · have hu' : conjUnipotent hMU a u ∉ B := by
        show conjUnipotent hMU a⁻¹ (conjUnipotent hMU a u) ∉ Γ
        rw [hinv]
        exact hu
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
  rw [hfun, hν.integral_comp a, integral_indicator hB, enorm_nnreal_mul]
  gcongr
  exact enorm_setIntegral_le_of_integral_eq_zero hf h0 hB hV

end Phi

section Factors

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] {M U U' : Subgroup G}

/-- The function `φ₁(a, m) = δ(m)^{1/2} ∫_Γ f₁(m a ū a⁻¹) dν(ū)` of the proof of
Proposition VIII.3.1, for `a, m ∈ M`. For Waldspurger's data `U = Ū`, `Γ = Γ̄` and
`δ = δ_{P̄} = δ_P^{-1}` on `M`, so `δ(m)^{1/2} = δ_P(m)^{-1/2}`. -/
def cuspidalFactor (hMU : M ≤ Subgroup.normalizer (U : Set G)) (ν : Measure U)
    (δ : M →* ℝ≥0ˣ) (Γ : Set U) (f₁ : G → ℂ) (a m : M) : ℂ :=
  ((NNReal.sqrt (δ m) : ℝ) : ℂ) *
    ∫ u : U, Γ.indicator (fun u => f₁ ((m : G) * conjUnipotent hMU a u)) u ∂ν

/-- The function `φ₂(a, m) = δ'(m)^{-1/2} ∫_A f₂(u m) dν'(u)` of the proof of
Proposition VIII.3.1. For Waldspurger's data `U' = U`, `A = a⁻¹ Γ a` and `δ' = δ_P`. -/
def unipotentFactor (ν' : Measure U') (δ' : M →* ℝ≥0ˣ) (A : Set U') (f₂ : G → ℂ)
    (m : M) : ℂ :=
  ((((NNReal.sqrt (δ' m))⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ u in A, f₂ ((u : G) * m) ∂ν'

end Factors

section Assembly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U U' : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {hMU' : M ≤ Subgroup.normalizer (U' : Set G)}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {ν' : Measure U'} {δ' : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM : M → ℝ} {KM : Subgroup M} [CompactSpace KM]
  [SecondCountableTopology M] {μM : Measure M} [μM.IsMulLeftInvariant]
  [μM.IsMulRightInvariant] [SFinite μM]

/-- The estimate of `J(a)` in the proof of Proposition VIII.3.1, for abstract data. Here `U`
plays `Ū` (with `ν = dū` and `δ = δ_{P̄}`), `U'` plays `U` (with `ν' = du` and
`δ' = δ_P`), `Γ ⊆ U` plays `Γ̄`, `A(a) ⊆ U'` plays `a⁻¹ Γ a`, `V(a) ⊆ U` plays `Ū_a`,
`t(a)` plays `δ (1 + σ(a))`, `T` plays `Ā⁺₀(α) ∩ G¹`, and
`φ₁(a, m') = δ(m')^{1/2} ∫_{Γ} f₁(m' a ū a⁻¹) dū`, `φ₂(a, m) = δ'(m)^{-1/2} ∫_{A(a)} f₂(u m) du`.
From inequalities (4), (5), (6), the averaging of `Convolution`-type weights on `M` and the
upper bound of Lemma II.1.1 for `M`, for every `r` there is `c` with
`∫_M |φ₁(a, a m a⁻¹)| |φ₂(a, m)| dm ≤ c e₀(a)² (1 + σ(a))^{-r}` for `a ∈ T`. -/
theorem lintegral_cuspidal_le {S : Set M} {e eM : M → ℝ} {w : U → ℝ}
    (hν : IsConjModulus hMU ν δ) (hδK : ∀ k ∈ KM, δ k = 1)
    (hcover : IsDoubleCosetCover KM S)
    (hΞK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, Ξ ((k₁ : G) * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, σ ((k₁ : G) * g * k₂) = σ g)
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (he : ∀ m ∈ S, 0 ≤ e m)
    (hw : ∀ u, 0 ≤ w u) (heM : ∀ m ∈ S, e m * NNReal.sqrt (δ m) ≤ eM m)
    (h44 : UnipotentXiBound Ξ σ S e w) (h31 : SigmaProductBound M U σ)
    (h11 : XiLowerBound ΞM S eM) (h42 : UnipotentWeightIntegrable ν w σ)
    (hν' : IsConjModulus hMU' ν' δ')
    (h45' : ConstantTermEstimate ν' δ' Ξ σ ΞM (fun m => σ m))
    (hwM : ConvolutionWeights μM KM ΞM (fun m => σ m))
    {T : Set M} {eA e₀ : M → ℝ} (hupM : XiUpperBound ΞM (fun m => σ m) T eA)
    (heA : ∀ a ∈ T, (((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) * eA a ^ 2 ≤ e₀ a ^ 2)
    {Γ : Set U} (hΓ : MeasurableSet Γ) {A : M → Set U'} {V : M → Set U} {t : M → ℝ}
    (hVt : ∀ a ∈ T, ∀ u ∈ V a, t a ≤ 1 + σ u)
    (hVK : ∀ a ∈ T, ∀ k ∈ KM, ∀ u, conjUnipotent hMU k u ∈ V a ↔ u ∈ V a)
    (hBV : ∀ a ∈ T, (conjUnipotent hMU a⁻¹ ⁻¹' Γ)ᶜ ⊆ V a)
    (ht : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ a ∈ T, δ₁ * (1 + σ a) ≤ t a)
    {f₁ f₂ : G → ℂ} (hf₁ : ∀ r, nu Ξ σ r f₁ < ⊤) (hf₂ : ∀ r, nu Ξ σ r f₂ < ⊤)
    (hint : ∀ m : M, Integrable (fun v : U => f₁ ((m : G) * v)) ν)
    (hcusp : ∀ m : M, ∫ v : U, f₁ ((m : G) * v) ∂ν = 0) (r : ℝ) :
    ∃ c : ℝ≥0, ∀ a ∈ T, ∫⁻ m : M,
      ‖cuspidalFactor hMU ν δ Γ f₁ a (a * m * a⁻¹)‖ₑ * ‖unipotentFactor ν' δ' (A a) f₂ m‖ₑ
          ∂μM ≤ c * ENNReal.ofReal (e₀ a ^ 2 * (1 + σ a) ^ (-r)) := by
  simp only [cuspidalFactor, unipotentFactor]
  obtain ⟨C, D, hupM⟩ := hupM
  obtain ⟨δ₁, hδ₁, ht⟩ := ht
  obtain ⟨d₀, hsqM⟩ := hwM.square
  set d'' := max (r + 2 * D) 0 with hd''_def
  have hd'' : 0 ≤ d'' := le_max_right _ _
  have hrd : r + 2 * D ≤ d'' := le_max_left _ _
  have hΞMK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m, ΞM (k₁ * m * k₂) = ΞM m :=
    fun k₁ hk₁ k₂ hk₂ m => by rw [hwM.xi_mul_right hk₂, hwM.xi_mul_left k₁ hk₁]
  obtain ⟨d₆, c₆, h6⟩ := setLIntegral_estimate_of_bounds hν hδK hcover hΞK hσK hΞMK
    hσ (fun m => (hwM.pos m).le) he hw heM h44 h31 h11 h42 0 hd''
  obtain ⟨d₄, c₄, h4⟩ := h45'.lintegral_mul_right_le hν' hΞ hσ (d₀ : ℝ)
  set ν₁ := nu Ξ σ d₆ f₁
  set ν₂ := nu Ξ σ d₄ f₂
  have hν₁ : ν₁ ≠ ⊤ := (hf₁ d₆).ne
  have hν₂ : ν₂ ≠ ⊤ := (hf₂ d₄).ne
  set X : ℝ≥0∞ := ν₁ * c₆ * (c₄ * ν₂) with hX_def
  have hX : X ≠ ⊤ := by
    simp only [hX_def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hν₁ ENNReal.coe_ne_top)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hν₂)
  have hpos : ∀ m : M, 0 < 1 + σ m := fun m => by linarith [hσ m]
  set W : M → ℝ≥0∞ := fun m => ENNReal.ofReal (ΞM m * (1 + σ m) ^ (-(d₀ : ℝ))) with hW_def
  have hσc : Continuous fun m : M => (1 + σ m) ^ (-(d₀ : ℝ)) :=
    (continuous_const.add hwM.continuous_sigma).rpow_const fun m => Or.inl (hpos m).ne'
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp (hwM.continuous_xi.mul hσc).measurable
  have hσr : ∀ k ∈ KM, ∀ m : M, σ ((m * k : M) : G) = σ m := fun k hk m => by
    have h := hσK 1 KM.one_mem k hk m
    simpa using h
  have hWl : ∀ k ∈ KM, ∀ m, W (k * m) = W m := fun k hk m => by
    simp only [hW_def, hwM.xi_mul_left k hk, hwM.sigma_mul_left k hk]
  have hWr : ∀ k ∈ KM, ∀ m, W (m * k) = W m := fun k hk m => by
    simp only [hW_def, hwM.xi_mul_right hk, hσr k hk]
  set IM : ℝ≥0∞ := ∫⁻ m, ENNReal.ofReal (ΞM m ^ 2 * (1 + σ m) ^ (-(d₀ : ℝ))) ∂μM
  have hIM : IM ≠ ⊤ := hsqM.ne
  have hIMW : ∫⁻ m, ENNReal.ofReal (ΞM m) * W m ∂μM = IM := by
    refine lintegral_congr fun m => ?_
    simp only [hW_def]
    rw [← ENNReal.ofReal_mul (hwM.pos m).le]
    congr 1
    ring
  set B : ℝ := δ₁ ^ (-d'') * C ^ 2 with hB_def
  have hB : 0 ≤ B := by positivity
  refine ⟨(X * IM * ENNReal.ofReal B).toNNReal, fun a ha => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.mul_ne_top hX hIM)
    ENNReal.ofReal_ne_top)]
  set δa : ℝ := (((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) with hδa_def
  have hδa : 0 ≤ δa := NNReal.coe_nonneg _
  have hta : 0 < t a := lt_of_lt_of_le (by have := hpos a; positivity) (ht a ha)
  set R : ℝ := δa * t a ^ (-d'') with hR_def
  have hR : 0 ≤ R := mul_nonneg hδa (Real.rpow_nonneg hta.le _)
  -- pointwise bound
  have hpt : ∀ m : M,
      ‖((NNReal.sqrt (δ (a * m * a⁻¹)) : ℝ) : ℂ) * ∫ u : U, Γ.indicator
          (fun u => f₁ (((a * m * a⁻¹ : M) : G) * conjUnipotent hMU a u)) u ∂ν‖ₑ *
        ‖((((NNReal.sqrt (δ' m))⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ u in A a, f₂ ((u : G) * m) ∂ν'‖ₑ ≤
      X * ENNReal.ofReal R * (ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m) := by
    intro m
    set m' := a * m * a⁻¹
    -- the factor `φ₁`, by (5) and (6)
    have h1 : ‖((NNReal.sqrt (δ m') : ℝ) : ℂ) * ∫ u : U, Γ.indicator
          (fun u => f₁ ((m' : G) * conjUnipotent hMU a u)) u ∂ν‖ₑ ≤
        ENNReal.ofReal δa * ν₁ * c₆ * ENNReal.ofReal (t a ^ (-d'')) *
          ENNReal.ofReal (ΞM m') := by
      rw [enorm_nnreal_mul]
      have h5 := hν.enorm_integral_conj_le a m' (hint m') (hcusp m') hΓ (hBV a ha)
      have h6' := h6 (V a) (t a) hta (hVt a ha) (hVK a ha) m'
      simp only [neg_zero, Real.rpow_zero, mul_one] at h6'
      have hind : ∫⁻ v : U, (V a).indicator (fun v => ‖f₁ ((m' : G) * v)‖ₑ) v ∂ν ≤
          ν₁ * ∫⁻ v : U, (V a).indicator (fun v : U => ENNReal.ofReal
            (Ξ ((m' : G) * v) * (1 + σ ((m' : G) * v)) ^ (-d₆))) v ∂ν := by
        rw [← lintegral_const_mul' _ _ hν₁]
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ V a
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
          exact enorm_le_nu_mul hΞ hσ f₁ d₆ _
        · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
      calc (NNReal.sqrt (δ m') : ℝ≥0∞) * ‖∫ u : U, Γ.indicator
            (fun u => f₁ ((m' : G) * conjUnipotent hMU a u)) u ∂ν‖ₑ
          ≤ (NNReal.sqrt (δ m') : ℝ≥0∞) * ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
              ∫⁻ v : U, (V a).indicator (fun v => ‖f₁ ((m' : G) * v)‖ₑ) v ∂ν) := by
            gcongr
        _ ≤ (NNReal.sqrt (δ m') : ℝ≥0∞) * ((((δ a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
              (ν₁ * ∫⁻ v : U, (V a).indicator (fun v : U => ENNReal.ofReal
                (Ξ ((m' : G) * v) * (1 + σ ((m' : G) * v)) ^ (-d₆))) v ∂ν)) := by
            gcongr
        _ = ENNReal.ofReal δa * ν₁ * ((NNReal.sqrt (δ m') : ℝ≥0∞) *
              ∫⁻ v : U, (V a).indicator (fun v : U => ENNReal.ofReal
                (Ξ ((m' : G) * v) * (1 + σ ((m' : G) * v)) ^ (-d₆))) v ∂ν) := by
            rw [hδa_def, ENNReal.ofReal_coe_nnreal]
            ring
        _ ≤ ENNReal.ofReal δa * ν₁ * (c₆ * ENNReal.ofReal (t a ^ (-d'')) *
              ENNReal.ofReal (ΞM m')) := by
            gcongr
        _ = ENNReal.ofReal δa * ν₁ * c₆ * ENNReal.ofReal (t a ^ (-d'')) *
              ENNReal.ofReal (ΞM m') := by ring
    -- the factor `φ₂`, by (4)
    have h2 : ‖((((NNReal.sqrt (δ' m))⁻¹ : ℝ≥0) : ℝ) : ℂ) *
          ∫ u in A a, f₂ ((u : G) * m) ∂ν'‖ₑ ≤ c₄ * ν₂ * W m := by
      rw [enorm_nnreal_mul]
      calc ((((NNReal.sqrt (δ' m))⁻¹ : ℝ≥0)) : ℝ≥0∞) * ‖∫ u in A a, f₂ ((u : G) * m) ∂ν'‖ₑ
          ≤ ((((NNReal.sqrt (δ' m))⁻¹ : ℝ≥0)) : ℝ≥0∞) *
              ∫⁻ u : U', ‖f₂ ((u : G) * m)‖ₑ ∂ν' := by
            gcongr
            exact (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_le_lintegral _ _)
        _ ≤ c₄ * ν₂ * W m := h4 f₂ hν₂ m
    calc _ ≤ (ENNReal.ofReal δa * ν₁ * c₆ * ENNReal.ofReal (t a ^ (-d'')) *
            ENNReal.ofReal (ΞM m')) * (c₄ * ν₂ * W m) := mul_le_mul' h1 h2
      _ = X * (ENNReal.ofReal δa * ENNReal.ofReal (t a ^ (-d''))) *
            (ENNReal.ofReal (ΞM m') * W m) := by
          rw [hX_def]
          ring
      _ = X * ENNReal.ofReal R * (ENNReal.ofReal (ΞM m') * W m) := by
          rw [← ENNReal.ofReal_mul hδa]
  have hRm : Measurable fun m : M => X * ENNReal.ofReal R *
      (ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m) := by
    refine Measurable.const_mul (Measurable.mul ?_ hWm) _
    exact ENNReal.measurable_ofReal.comp
      (hwM.continuous_xi.comp ((continuous_const.mul continuous_id).mul continuous_const)).measurable
  -- the final real inequality
  have hfin : R * ΞM a ^ 2 ≤ B * (e₀ a ^ 2 * (1 + σ a) ^ (-r)) := by
    have hσa := hσ a
    have h1 : t a ^ (-d'') ≤ δ₁ ^ (-d'') * (1 + σ a) ^ (-d'') := by
      rw [← Real.mul_rpow hδ₁.le (hpos a).le]
      exact Real.rpow_le_rpow_of_nonpos (by have := hpos a; positivity) (ht a ha)
        (by linarith)
    have h2 : ΞM a ^ 2 ≤ C ^ 2 * eA a ^ 2 * (1 + σ a) ^ (2 * D) := by
      have h := pow_le_pow_left₀ (hwM.pos a).le (hupM a ha) 2
      have h' : ((1 + σ a) ^ D) ^ 2 = (1 + σ a) ^ (2 * D) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos a).le]
        ring_nf
      calc ΞM a ^ 2 ≤ (C * eA a * (1 + σ a) ^ D) ^ 2 := h
        _ = C ^ 2 * eA a ^ 2 * ((1 + σ a) ^ D) ^ 2 := by ring
        _ = C ^ 2 * eA a ^ 2 * (1 + σ a) ^ (2 * D) := by rw [h']
    have h3 : (1 + σ a) ^ (-d'') * (1 + σ a) ^ (2 * D) ≤ (1 + σ a) ^ (-r) := by
      rw [← Real.rpow_add (hpos a)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hp1 : 0 ≤ (1 + σ a) ^ (-d'') := Real.rpow_nonneg (hpos a).le _
    have hp2 : 0 ≤ (1 + σ a) ^ (2 * D) := Real.rpow_nonneg (hpos a).le _
    have hp3 : 0 ≤ δ₁ ^ (-d'') := Real.rpow_nonneg hδ₁.le _
    calc R * ΞM a ^ 2 = δa * t a ^ (-d'') * ΞM a ^ 2 := by rw [hR_def]
      _ ≤ δa * (δ₁ ^ (-d'') * (1 + σ a) ^ (-d'')) *
            (C ^ 2 * eA a ^ 2 * (1 + σ a) ^ (2 * D)) := by
          gcongr
      _ = δ₁ ^ (-d'') * C ^ 2 * (δa * eA a ^ 2) *
            ((1 + σ a) ^ (-d'') * (1 + σ a) ^ (2 * D)) := by ring
      _ ≤ δ₁ ^ (-d'') * C ^ 2 * e₀ a ^ 2 * (1 + σ a) ^ (-r) := by
          have hB' : 0 ≤ δ₁ ^ (-d'') * C ^ 2 := by positivity
          have he0 : 0 ≤ e₀ a ^ 2 := sq_nonneg _
          have hprod : 0 ≤ (1 + σ a) ^ (-d'') * (1 + σ a) ^ (2 * D) := mul_nonneg hp1 hp2
          calc δ₁ ^ (-d'') * C ^ 2 * (δa * eA a ^ 2) *
                ((1 + σ a) ^ (-d'') * (1 + σ a) ^ (2 * D))
              ≤ δ₁ ^ (-d'') * C ^ 2 * e₀ a ^ 2 *
                ((1 + σ a) ^ (-d'') * (1 + σ a) ^ (2 * D)) := by
                gcongr
                exact heA a ha
            _ ≤ δ₁ ^ (-d'') * C ^ 2 * e₀ a ^ 2 * (1 + σ a) ^ (-r) := by
                gcongr
      _ = B * (e₀ a ^ 2 * (1 + σ a) ^ (-r)) := by rw [hB_def]; ring
  calc _ ≤ ∫⁻ m : M, X * ENNReal.ofReal R *
          (ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m) ∂μM := lintegral_mono hpt
    _ = X * ENNReal.ofReal R * ∫⁻ m : M, ENNReal.ofReal (ΞM (a * m * a⁻¹)) * W m ∂μM :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hX ENNReal.ofReal_ne_top)
    _ = X * IM * ENNReal.ofReal (R * ΞM a ^ 2) := by
        rw [hwM.lintegral_xi_mul_mul hWm hWl hWr, hwM.xi_inv, hIMW, ENNReal.ofReal_mul hR,
          ← ENNReal.ofReal_mul (hwM.pos a).le, ← sq]
        ring
    _ ≤ X * IM * ENNReal.ofReal (B * (e₀ a ^ 2 * (1 + σ a) ^ (-r))) := by
        gcongr
    _ = X * IM * ENNReal.ofReal B * ENNReal.ofReal (e₀ a ^ 2 * (1 + σ a) ^ (-r)) := by
        rw [ENNReal.ofReal_mul hB]
        ring

end Assembly

section Conclusion

variable {G : Type u} [Group G] [MeasurableSpace G] {M : Subgroup G} {μ : Measure G}
  {μM : Measure M}

/-- The conclusion of Proposition VIII.3.1: for every `r` there is `c` with
`|∫_G f₁(a g a⁻¹) f₂(g) dμ(g)| ≤ c e(a)² (1 + σ(a))^{-r}` for all `a ∈ T`. For
Waldspurger's data `T = Ā⁺₀ ∩ G¹` and `e = δ₀^{1/2}`, so `e(a)² = δ₀(a)`. -/
def ConjugationIntegralBound (μ : Measure G) (T : Set M) (f₁ f₂ : G → ℂ) (e : M → ℝ)
    (σ : G → ℝ) : Prop :=
  ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T, ‖∫ g, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ‖ₑ ≤
    c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))

/-- Proposition VIII.3.1 from its two halves. If, for `a ∈ T`,
`∫_G f₁(a g a⁻¹) f₂(g) dg = ∫_{S(a)} f₁(a g a⁻¹) f₂(g) dg + γ ∫_M φ₁(a, m) φ₂(a, m) dm`
(for Waldspurger's data, the decomposition `G = S(a) ⊔ a⁻¹ Γ a M Γ̄` and the integration
formula of I.1 on `U M Ū`), and both pieces satisfy bounds of the form
`c e(a)² (1 + σ(a))^{-r}` (inequality (3), `ConvolutionWeights.lintegral_conj_mul_le`, and
the estimate of `J(a)`, `lintegral_cuspidal_le`), then
`|∫_G f₁(a g a⁻¹) f₂(g) dg| ≤ c e(a)² (1 + σ(a))^{-r}` on `T`. -/
theorem enorm_integral_conj_le_of_split {T : Set M} {S : M → Set G} {f₁ f₂ : G → ℂ}
    {φ₁ φ₂ : M → M → ℂ} {γ : ℂ} {e : M → ℝ} {σ : G → ℝ} {r : ℝ}
    (hsplit : ∀ a ∈ T, ∫ g, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ =
      ∫ g in S a, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ + γ * ∫ m, φ₁ a m * φ₂ a m ∂μM)
    (h3 : ∃ c : ℝ≥0, ∀ a ∈ T, ∫⁻ g in S a, ‖f₁ ((a : G) * g * (a : G)⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)))
    (hJ : ∃ c : ℝ≥0, ∀ a ∈ T, ∫⁻ m, ‖φ₁ a m‖ₑ * ‖φ₂ a m‖ₑ ∂μM ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))) :
    ∃ c : ℝ≥0, ∀ a ∈ T, ‖∫ g, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ‖ₑ ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) := by
  obtain ⟨c₃, h3⟩ := h3
  obtain ⟨cJ, hJ⟩ := hJ
  refine ⟨c₃ + ‖γ‖₊ * cJ, fun a ha => ?_⟩
  rw [hsplit a ha]
  calc ‖∫ g in S a, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ +
        γ * ∫ m, φ₁ a m * φ₂ a m ∂μM‖ₑ
      ≤ ‖∫ g in S a, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ‖ₑ +
          ‖γ‖ₑ * ‖∫ m, φ₁ a m * φ₂ a m ∂μM‖ₑ := by
        refine (enorm_add_le _ _).trans ?_
        rw [enorm_mul]
    _ ≤ ∫⁻ g in S a, ‖f₁ ((a : G) * g * (a : G)⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ +
          ‖γ‖ₑ * ∫⁻ m, ‖φ₁ a m‖ₑ * ‖φ₂ a m‖ₑ ∂μM := by
        gcongr
        · exact (enorm_integral_le_lintegral_enorm _).trans_eq (by simp only [enorm_mul])
        · exact (enorm_integral_le_lintegral_enorm _).trans_eq (by simp only [enorm_mul])
    _ ≤ c₃ * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) +
          ‖γ‖ₑ * (cJ * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))) := by
        gcongr
        · exact h3 a ha
        · exact hJ a ha
    _ = ((c₃ + ‖γ‖₊ * cJ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) := by
        rw [ENNReal.coe_add, ENNReal.coe_mul, enorm_eq_nnnorm]
        ring

/-- Proposition VIII.3.1 (`ConjugationIntegralBound`) from the decomposition `hsplit` and
the two estimates for every `r`. -/
theorem conjugationIntegralBound_of_split {T : Set M} {S : M → Set G} {f₁ f₂ : G → ℂ}
    {φ₁ φ₂ : M → M → ℂ} {γ : ℂ} {e : M → ℝ} {σ : G → ℝ}
    (hsplit : ∀ a ∈ T, ∫ g, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ =
      ∫ g in S a, f₁ ((a : G) * g * (a : G)⁻¹) * f₂ g ∂μ + γ * ∫ m, φ₁ a m * φ₂ a m ∂μM)
    (h3 : ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T,
      ∫⁻ g in S a, ‖f₁ ((a : G) * g * (a : G)⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ ≤
        c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)))
    (hJ : ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T, ∫⁻ m, ‖φ₁ a m‖ₑ * ‖φ₂ a m‖ₑ ∂μM ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))) :
    ConjugationIntegralBound μ T f₁ f₂ e σ :=
  fun r => enorm_integral_conj_le_of_split (φ₁ := φ₁) (φ₂ := φ₂) hsplit (h3 r) (hJ r)

end Conclusion

end Langlands.HarishChandraSchwartz
