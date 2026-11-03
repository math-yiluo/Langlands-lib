import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd

/-! # Proposition II.4.5 from the lemmas of II.1, II.3 and II.4

Waldspurger 2003, Proposition II.4.5: for every `d` there are `d'` and `c` with
`δ_P(m)^{-1/2} ∫_Ū Ξ(m ū) (1 + σ(m ū))^{-d'} dū ≤ c Ξ^M(m) (1 + σ(m))^{-d}` for `m ∈ M`.
The published module `ConstantTerm` takes this estimate (for the opposite parabolic
subgroup) as the hypothesis `ConstantTermEstimate`. This module proves
`ConstantTermEstimate` from the ingredients of Waldspurger's proof, each stated as a
Prop-valued hypothesis on abstract data:

* `UnipotentXiBound` (Lemma II.4.4) on a set `S ⊆ M` of Cartan representatives;
* `SigmaProductBound` (the second inequality of Lemma II.3.1);
* `XiLowerBound` (the lower bound of Lemma II.1.1, for `M`);
* `UnipotentWeightIntegrable` (Lemma II.4.2);
* `IsDoubleCosetCover` (`M = (K ∩ M) S (K ∩ M)`, from the Cartan decomposition of `M`),
  with bi-invariance of `Ξ`, `σ`, `Ξ^M` and the modulus relation `IsConjModulus`.

Here `U` is the subgroup over which the constant term integrates (Waldspurger's `Ū`),
`δ` is the character of the constant term along `M U` (Waldspurger's `δ_P^{-1}` on `M`),
and `σ^M` is the restriction of `σ` to `M`, as in the article.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section Defs

/-- `S` meets every double coset of `K`: every `m` is `k₁ s k₂` with `k₁, k₂ ∈ K` and
`s ∈ S`. For a Levi subgroup `M` and `K ∩ M` this is the covering part of the Cartan
decomposition `M = (K ∩ M) M̄^{M+}_0 (K ∩ M)` (Waldspurger I.1 (4) for `M`). -/
def IsDoubleCosetCover {H : Type*} [Group H] (K : Subgroup H) (S : Set H) : Prop :=
  ∀ h : H, ∃ k₁ ∈ K, ∃ s ∈ S, ∃ k₂ ∈ K, h = k₁ * s * k₂

/-- The lower bound of Lemma II.1.1: there is `C` with `e(x) ≤ C Ξ(x)` for `x ∈ S`. For
Waldspurger's group `M`, `Ξ = Ξ^M`, `S = M̄^{M+}_0` and `e = (δ^M_0)^{1/2}`. -/
def XiLowerBound {X : Type*} (Ξ : X → ℝ) (S : Set X) (e : X → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ S, e x ≤ C * Ξ x

variable {G : Type u} [Group G] {M U : Subgroup G}

/-- Lemma II.4.4: there are `D` and `c` with `Ξ(m u) ≤ c e(m) w(u) (1 + σ(m u))^D` for
`m ∈ S` and `u ∈ U`. In Waldspurger's lemma `S = M_0`, `U = Ū`, `e(m) = δ_0(m)^{1/2}` and
`w(ū) = δ_0(m_0(ū))^{1/2}`. -/
def UnipotentXiBound (Ξ σ : G → ℝ) (S : Set M) (e : M → ℝ) (w : U → ℝ) : Prop :=
  ∃ D c : ℝ, ∀ m ∈ S, ∀ u : U,
    Ξ ((m : G) * u) ≤ c * e m * w u * (1 + σ ((m : G) * u)) ^ D

variable (M U) in
/-- The second inequality of Lemma II.3.1: there is `C > 0` with
`C (1 + sup(σ(m), σ(u))) ≤ 1 + σ(m u)` for `m ∈ M` and `u ∈ U`. Waldspurger states it
for a semi-standard parabolic subgroup `P = M U`; Proposition II.4.5 uses it for the
opposite parabolic subgroup `M Ū`. -/
def SigmaProductBound (σ : G → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : M, ∀ u : U,
    C * (1 + max (σ m) (σ u)) ≤ 1 + σ ((m : G) * u)

/-- Lemma II.4.2: for some `d`, `∫_U w(u) (1 + σ(u))^{-d} dν(u) < ∞`. In Waldspurger's
lemma `U = Ū` and `w(ū) = δ_0(m_0(ū))^{1/2}`. -/
def UnipotentWeightIntegrable [MeasurableSpace G] (ν : Measure U) (w : U → ℝ) (σ : G → ℝ) :
    Prop :=
  ∃ d : ℝ, ∫⁻ u, ENNReal.ofReal (w u * (1 + σ u) ^ (-d)) ∂ν < ⊤

end Defs

section Modulus

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}

/-- Change of variables `u ↦ m u m⁻¹` in a lower integral:
`∫⁻_U φ(m u m⁻¹) dν(u) = δ(m)⁻¹ ∫⁻_U φ dν`. -/
theorem IsConjModulus.lintegral_comp (hν : IsConjModulus hMU ν δ) (m : M) (φ : U → ℝ≥0∞) :
    ∫⁻ u, φ (conjUnipotent hMU m u) ∂ν =
      (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ u, φ u ∂ν := by
  calc ∫⁻ u, φ (conjUnipotent hMU m u) ∂ν
      = ∫⁻ u, φ ((conjUnipotentHomeomorph hMU m).toMeasurableEquiv u) ∂ν := rfl
    _ = ∫⁻ u, φ u ∂(ν.map (conjUnipotentHomeomorph hMU m).toMeasurableEquiv) :=
        (lintegral_map_equiv _ _).symm
    _ = ∫⁻ u, φ u ∂(ν.map (conjUnipotent hMU m)) := rfl
    _ = _ := by rw [hν m, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

end Modulus

section Estimate

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {M U : Subgroup G}
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM : M → ℝ} {KM : Subgroup M}

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- The scalar inequality behind Proposition II.4.5: if `C (1 + sup(a, b)) ≤ 1 + t` with
`C > 0` and `a, b ≥ 0`, then `(1 + t)^{-2r} ≤ C^{-2r} (1 + a)^{-r} (1 + b)^{-r}` for
`r ≥ 0`. -/
theorem one_add_rpow_neg_le {a b t C r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 < C)
    (hr : 0 ≤ r) (h : C * (1 + max a b) ≤ 1 + t) :
    (1 + t) ^ (-(2 * r)) ≤ C ^ (-(2 * r)) * ((1 + a) ^ (-r) * (1 + b) ^ (-r)) := by
  have hmax : 0 < 1 + max a b := by positivity
  have h1 : (1 + t) ^ (-(2 * r)) ≤ (C * (1 + max a b)) ^ (-(2 * r)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
  have h2 : (1 + max a b) ^ (-(2 * r)) ≤ (1 + a) ^ (-r) * (1 + b) ^ (-r) := by
    rw [show -(2 * r) = 2 * -r by ring, Real.rpow_mul hmax.le, Real.rpow_two,
      ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [sq]
    exact mul_le_mul (by simp) (by simp) (by positivity) hmax.le
  rw [Real.mul_rpow hC.le hmax.le] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- Waldspurger, Proposition II.4.5 (for the parabolic subgroup `M U`, with `σ^M` the
restriction of `σ`), from Lemma II.4.4 (`UnipotentXiBound` on `S`), the second inequality
of Lemma II.3.1 (`SigmaProductBound`), the lower bound of Lemma II.1.1 for `M`
(`XiLowerBound` on `S`, with `e(m) δ(m)^{1/2} ≤ e^M(m)`), Lemma II.4.2
(`UnipotentWeightIntegrable`) and the covering `M = K_M S K_M`, under bi-invariance of
`Ξ`, `σ` and `Ξ^M` by `K_M`, the modulus relation for `ν` and triviality of `δ` on `K_M`. -/
theorem constantTermEstimate_of_bounds {S : Set M} {e eM : M → ℝ} {w : U → ℝ}
    (hν : IsConjModulus hMU ν δ) (hδK : ∀ k ∈ KM, δ k = 1)
    (hcover : IsDoubleCosetCover KM S)
    (hΞK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, Ξ ((k₁ : G) * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ g, σ ((k₁ : G) * g * k₂) = σ g)
    (hΞMK : ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m, ΞM (k₁ * m * k₂) = ΞM m)
    (hσ : ∀ g, 0 ≤ σ g) (hΞM : ∀ m, 0 ≤ ΞM m) (he : ∀ m ∈ S, 0 ≤ e m)
    (hw : ∀ u, 0 ≤ w u) (heM : ∀ m ∈ S, e m * NNReal.sqrt (δ m) ≤ eM m)
    (h44 : UnipotentXiBound Ξ σ S e w) (h31 : SigmaProductBound M U σ)
    (h11 : XiLowerBound ΞM S eM) (h42 : UnipotentWeightIntegrable ν w σ) :
    ConstantTermEstimate ν δ Ξ σ ΞM (fun m => σ m) := by
  obtain ⟨D, c₁, h44⟩ := h44
  obtain ⟨C₂, hC₂, h31⟩ := h31
  obtain ⟨C₃, h11⟩ := h11
  obtain ⟨d₂, hI₂⟩ := h42
  intro d
  set r := max (max d d₂) 0 with hr_def
  have hr : 0 ≤ r := le_max_right _ _
  have hdr : d ≤ r := (le_max_left _ _).trans (le_max_left _ _)
  have hd₂r : d₂ ≤ r := (le_max_right _ _).trans (le_max_left _ _)
  set c₁' := max c₁ 0
  set C₃' := max C₃ 0
  set K : ℝ := c₁' * C₂ ^ (-(2 * r)) * C₃'
  have hK : 0 ≤ K := by positivity
  set I : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal (w u * (1 + σ u) ^ (-r)) ∂ν
  have hI : I ≠ ⊤ := by
    refine (lt_of_le_of_lt (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_) hI₂).ne
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hσ u]) (by linarith)) (hw u)
  refine ⟨D + 2 * r, (Real.toNNReal K) * I.toNNReal, fun m => ?_⟩
  -- the bound at the points of `S`
  have key : ∀ s ∈ S, (NNReal.sqrt (δ s) : ℝ≥0∞) *
      ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
      ≤ ENNReal.ofReal K * I * ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
    intro s hs
    set A : ℝ := c₁' * C₂ ^ (-(2 * r)) * e s * (1 + σ s) ^ (-r)
    have hA : 0 ≤ A := by
      have := he s hs
      have := hσ s
      positivity
    have hpt : ∀ u : U, Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)) ≤
        A * (w u * (1 + σ u) ^ (-r)) := by
      intro u
      have ht : 0 < 1 + σ ((s : G) * u) := by linarith [hσ ((s : G) * u)]
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
              rw [mul_assoc, ← Real.rpow_add ht]
              ring_nf
      have h3 := one_add_rpow_neg_le (hσ s) (hσ u) hC₂ hr (h31 s u)
      calc Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))
          ≤ c₁' * e s * w u * (1 + σ ((s : G) * u)) ^ (-(2 * r)) := h2
        _ ≤ c₁' * e s * w u * (C₂ ^ (-(2 * r)) * ((1 + σ s) ^ (-r) * (1 + σ u) ^ (-r))) := by
            have := he s hs
            have := hw u
            gcongr
        _ = A * (w u * (1 + σ u) ^ (-r)) := by ring
    have hint : ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
        (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν ≤ ENNReal.ofReal A * I := by
      calc ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
          ≤ ∫⁻ u : U, ENNReal.ofReal A * ENNReal.ofReal (w u * (1 + σ u) ^ (-r)) ∂ν := by
            refine lintegral_mono fun u => ?_
            rw [← ENNReal.ofReal_mul hA]
            exact ENNReal.ofReal_le_ofReal (hpt u)
        _ = ENNReal.ofReal A * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
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
          ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
            (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν
        ≤ (NNReal.sqrt (δ s) : ℝ≥0∞) * (ENNReal.ofReal A * I) := by gcongr
      _ = ENNReal.ofReal ((NNReal.sqrt (δ s) : ℝ) * A) * I := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, mul_assoc]
      _ ≤ ENNReal.ofReal (K * (ΞM s * (1 + σ s) ^ (-d))) * I := by
          gcongr
      _ = ENNReal.ofReal K * I * ENNReal.ofReal (ΞM s * (1 + σ s) ^ (-d)) := by
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
  have hint : ∫⁻ u : U, ENNReal.ofReal (Ξ (((k₁ * s * k₂ : M) : G) * u) *
        (1 + σ (((k₁ * s * k₂ : M) : G) * u)) ^ (-(D + 2 * r))) ∂ν =
      ∫⁻ u : U, ENNReal.ofReal (Ξ ((s : G) * u) *
        (1 + σ ((s : G) * u)) ^ (-(D + 2 * r))) ∂ν := by
    simp only [hfun, hΞK k₁ hk₁ k₂ hk₂, hσK k₁ hk₁ k₂ hk₂]
    rw [hν.lintegral_comp k₂
      (fun u => ENNReal.ofReal (Ξ ((s : G) * u) * (1 + σ ((s : G) * u)) ^ (-(D + 2 * r)))),
      hδK k₂ hk₂]
    simp
  have hRHS : ΞM (k₁ * s * k₂) * (1 + σ ((k₁ * s * k₂ : M) : G)) ^ (-d) =
      ΞM s * (1 + σ s) ^ (-d) := by
    rw [hΞMK k₁ hk₁ k₂ hk₂, Subgroup.coe_mul, Subgroup.coe_mul, hσK k₁ hk₁ k₂ hk₂]
  rw [hδ, hint, hRHS, ENNReal.coe_mul, ENNReal.coe_toNNReal hI]
  exact key s hs

end Estimate

end Langlands.HarishChandraSchwartz
