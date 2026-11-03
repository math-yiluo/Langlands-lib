import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution

/-! # The projection `p_χ` (Waldspurger VIII.4)

Waldspurger 2003, VIII.4: for a unitary character `χ` of `A_G` and `f ∈ C(G)`,
`(p_χ f)(g) = ∫_{A_G} χ^{-1}(a) f(a g) da`, an absolutely convergent integral; `p_χ f` is
bi-invariant under a compact open subgroup and `χ`-covariant. In the proof of Proposition
VIII.4.1 the elements of `p_χ(°C(G))` satisfy `|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` on `G¹`, for
every `r`. This module proves these facts for abstract data: a subgroup `A` with a measure
`μ_A`, weights `Ξ`, `σ` satisfying the hypotheses `CentralWeights`, and a unitary measurable
character `χ`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

/-- For `x, y ≥ 1`, `C > 0`, `t ≥ 0` and `x + y - 1 ≤ C z`:
`z^{-2t} ≤ (C²)^t x^{-t} y^{-t}`. -/
theorem rpow_neg_two_mul_le {x y z C t : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hC : 0 < C)
    (ht : 0 ≤ t) (h : x + y - 1 ≤ C * z) :
    z ^ (-(2 * t)) ≤ (C ^ 2) ^ t * (x ^ (-t) * y ^ (-t)) := by
  have hz : 0 < z := pos_of_mul_pos_right (by linarith) hC.le
  have hxy : x * y / C ^ 2 ≤ z ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : x * y ≤ (x + y - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
    have h2 : (x + y - 1) ^ 2 ≤ (C * z) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
    nlinarith
  have hpos : 0 < x * y / C ^ 2 := div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  calc z ^ (-(2 * t)) = (z ^ 2) ^ (-t) := by
        rw [show -(2 * t) = (2 : ℝ) * (-t) by ring, Real.rpow_mul hz.le, Real.rpow_two]
    _ ≤ (x * y / C ^ 2) ^ (-t) := Real.rpow_le_rpow_of_nonpos hpos hxy (by linarith)
    _ = (C ^ 2) ^ t * (x ^ (-t) * y ^ (-t)) := by
        rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by linarith) (by linarith),
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ C ^ 2), div_inv_eq_mul, mul_comm]

section Weights

variable {G : Type u} [Group G] {A : Subgroup G} [MeasurableSpace A]

/-- Hypotheses on the weights `Ξ`, `σ` relative to a subgroup `A` of `G` with a measure `μ_A`
(for Waldspurger's projection `p_χ` of VIII.4, `A = A_G`): `Ξ > 0`, `σ ≥ 0`,
`Ξ(a g) = Ξ(g)` and `1 + σ(a) ≤ (1 + σ(a g)) (1 + σ(g))` for `a ∈ A`, and
`∫_A (1 + σ(a))^{-r₀} dμ_A(a) < ∞` for some `r₀`. -/
structure CentralWeights (μA : Measure A) (Ξ σ : G → ℝ) : Prop where
  pos : ∀ g, 0 < Ξ g
  nonneg : ∀ g, 0 ≤ σ g
  xi_mul : ∀ (a : A) (g : G), Ξ ((a : G) * g) = Ξ g
  one_add_le : ∀ (a : A) (g : G), 1 + σ a ≤ (1 + σ ((a : G) * g)) * (1 + σ g)
  integrable : ∃ r₀ : ℝ, ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-r₀)) ∂μA < ⊤

/-- A unitary measurable character `χ : A → ℂˣ` (for Waldspurger, an element of `Â_G`). -/
structure IsUnitaryCharacter (χ : A →* ℂˣ) : Prop where
  norm_eq_one : ∀ a, ‖(χ a : ℂ)‖ = 1
  measurable : Measurable fun a => (χ a : ℂ)

/-- Waldspurger's `p_χ` (VIII.4): `(p_χ f)(g) = ∫_A χ(a)⁻¹ f(a g) dμ_A(a)`. -/
def centralProjection (μA : Measure A) (χ : A →* ℂˣ) (f : G → ℂ) (g : G) : ℂ :=
  ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g) ∂μA

variable {μA : Measure A} {Ξ σ : G → ℝ} {χ : A →* ℂˣ}

namespace IsUnitaryCharacter

theorem norm_inv (hχ : IsUnitaryCharacter χ) (a : A) : ‖(((χ a)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
  rw [Units.val_inv_eq_inv_val, _root_.norm_inv, hχ.norm_eq_one, inv_one]

theorem enorm_inv (hχ : IsUnitaryCharacter χ) (a : A) : ‖(((χ a)⁻¹ : ℂˣ) : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, hχ.norm_inv, ENNReal.ofReal_one]

theorem measurable_inv (hχ : IsUnitaryCharacter χ) :
    Measurable fun a => (((χ a)⁻¹ : ℂˣ) : ℂ) := by
  simp_rw [Units.val_inv_eq_inv_val]
  exact hχ.measurable.inv

end IsUnitaryCharacter

namespace CentralWeights

/-- `(1 + σ(a g))^{-s} ≤ (1 + σ(g))^s (1 + σ(a))^{-s}` for `a ∈ A` and `s ≥ 0`. -/
theorem rpow_neg_le (hw : CentralWeights μA Ξ σ) {s : ℝ} (hs : 0 ≤ s) (a : A) (g : G) :
    (1 + σ ((a : G) * g)) ^ (-s) ≤ (1 + σ g) ^ s * (1 + σ a) ^ (-s) := by
  have hg : 0 < 1 + σ g := by linarith [hw.nonneg g]
  have ha : 0 < 1 + σ a := by linarith [hw.nonneg a]
  have hle : (1 + σ a) / (1 + σ g) ≤ 1 + σ ((a : G) * g) :=
    (div_le_iff₀ hg).mpr (hw.one_add_le a g)
  calc (1 + σ ((a : G) * g)) ^ (-s) ≤ ((1 + σ a) / (1 + σ g)) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (div_pos ha hg) hle (neg_nonpos.mpr hs)
    _ = (1 + σ g) ^ s * (1 + σ a) ^ (-s) := by
        rw [Real.div_rpow ha.le hg.le, Real.rpow_neg hg.le, div_inv_eq_mul, mul_comm]

/-- The pointwise bound `|f(a g)| ≤ ν_s(f) Ξ(g) (1 + σ(g))^s (1 + σ(a))^{-s}` for `s ≥ 0`. -/
theorem enorm_le (hw : CentralWeights μA Ξ σ) {f : G → ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hf : nu Ξ σ s f ≠ ⊤) (a : A) (g : G) :
    ‖f ((a : G) * g)‖ₑ ≤
      nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s * (1 + σ a) ^ (-s)) := by
  have h := norm_le_of_nu hw.pos hw.nonneg hf ((a : G) * g)
  rw [hw.xi_mul] at h
  have h' : ‖f ((a : G) * g)‖ ≤
      (nu Ξ σ s f).toReal * (Ξ g * (1 + σ g) ^ s * (1 + σ a) ^ (-s)) := by
    refine h.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hw.rpow_neg_le hs a g) (hw.pos g).le
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hf, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal h'

/-- `∫_A |f(a g)| dμ_A ≤ ν_s(f) Ξ(g) (1 + σ(g))^s ∫_A (1 + σ(a))^{-s} dμ_A` for `s ≥ 0`. -/
theorem lintegral_enorm_le (hw : CentralWeights μA Ξ σ) {f : G → ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hf : nu Ξ σ s f ≠ ⊤) (g : G) :
    ∫⁻ a, ‖f ((a : G) * g)‖ₑ ∂μA ≤ nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) *
      ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA := by
  have hg : 0 ≤ Ξ g * (1 + σ g) ^ s :=
    mul_nonneg (hw.pos g).le (Real.rpow_nonneg (by linarith [hw.nonneg g]) _)
  calc ∫⁻ a, ‖f ((a : G) * g)‖ₑ ∂μA
      ≤ ∫⁻ a, nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) *
          ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA := by
        refine lintegral_mono fun a => (hw.enorm_le hs hf a g).trans_eq ?_
        rw [ENNReal.ofReal_mul hg, mul_assoc]
    _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top hf ENNReal.ofReal_ne_top)

/-- Some `s ≥ 0` has `∫_A (1 + σ(a))^{-s} dμ_A < ∞`. -/
theorem exists_lintegral_lt_top (hw : CentralWeights μA Ξ σ) :
    ∃ s : ℝ, 0 ≤ s ∧ ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA < ⊤ := by
  obtain ⟨r₀, h⟩ := hw.integrable
  refine ⟨max r₀ 0, le_max_right _ _, lt_of_le_of_lt (lintegral_mono fun a => ?_) h⟩
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
    (by linarith [hw.nonneg a]) (neg_le_neg (le_max_left _ _)))

/-- For `f` with all `ν_r(f)` finite and unitary `χ`, `|p_χ f(g)| ≤ ∫_A |f(a g)| dμ_A`, and
this is at most `ν_s(f) Ξ(g) (1 + σ(g))^s ∫_A (1 + σ(a))^{-s} dμ_A` for `s ≥ 0`. -/
theorem enorm_centralProjection_le (hw : CentralWeights μA Ξ σ) (hχ : IsUnitaryCharacter χ)
    {f : G → ℂ} {s : ℝ} (hs : 0 ≤ s) (hf : nu Ξ σ s f ≠ ⊤) (g : G) :
    ‖centralProjection μA χ f g‖ₑ ≤ nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) *
      ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq_of_le ?_ (hw.lintegral_enorm_le hs hf g))
  refine lintegral_congr fun a => ?_
  rw [enorm_mul, hχ.enorm_inv, one_mul]

/-- From the proof of Proposition VIII.4.1: if `1 + σ(g) + σ(a) ≤ C (1 + σ(a g))` for all
`g ∈ S` and `a ∈ A` (for Waldspurger, `S = G¹`), then for `f` with all `ν_r(f)` finite and
every `r` there is a finite `c` with `|p_χ f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` on `S`. -/
theorem enorm_centralProjection_le_rpow_neg (hw : CentralWeights μA Ξ σ)
    (hχ : IsUnitaryCharacter χ) {S : Set G} {C : ℝ} (hC : 0 < C)
    (hS : ∀ g ∈ S, ∀ a : A, 1 + σ g + σ a ≤ C * (1 + σ ((a : G) * g)))
    {f : G → ℂ} (hf : ∀ r, nu Ξ σ r f < ⊤) (r : ℝ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ g ∈ S,
      ‖centralProjection μA χ f g‖ₑ ≤ c * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) := by
  obtain ⟨r₀, hI⟩ := hw.integrable
  set t := max (max r r₀) 0
  have ht : 0 ≤ t := le_max_right _ _
  have hfs : nu Ξ σ (2 * t) f ≠ ⊤ := (hf _).ne
  have hCt : 0 ≤ (C ^ 2) ^ t := Real.rpow_nonneg (sq_nonneg C) t
  refine ⟨nu Ξ σ (2 * t) f * ENNReal.ofReal ((C ^ 2) ^ t) *
    ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-r₀)) ∂μA,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hfs ENNReal.ofReal_ne_top) hI.ne, fun g hg => ?_⟩
  have hx : 1 ≤ 1 + σ g := by linarith [hw.nonneg g]
  have hΞ : 0 ≤ Ξ g * (1 + σ g) ^ (-r) :=
    mul_nonneg (hw.pos g).le (Real.rpow_nonneg (by linarith) _)
  have hpt : ∀ a : A, ‖f ((a : G) * g)‖ₑ ≤
      nu Ξ σ (2 * t) f * ENNReal.ofReal ((C ^ 2) ^ t) *
        ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) * ENNReal.ofReal ((1 + σ a) ^ (-r₀)) := by
    intro a
    have h := norm_le_of_nu hw.pos hw.nonneg hfs ((a : G) * g)
    rw [hw.xi_mul] at h
    have hy : 1 ≤ 1 + σ a := by linarith [hw.nonneg a]
    have hz := rpow_neg_two_mul_le (z := 1 + σ ((a : G) * g)) hx hy hC ht
      (by linarith [hS g hg a])
    have hxr : (1 + σ g) ^ (-t) ≤ (1 + σ g) ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hx
        (neg_le_neg ((le_max_left r r₀).trans (le_max_left _ 0)))
    have hyr : (1 + σ a) ^ (-t) ≤ (1 + σ a) ^ (-r₀) :=
      Real.rpow_le_rpow_of_exponent_le hy
        (neg_le_neg ((le_max_right r r₀).trans (le_max_left _ 0)))
    have hreal : ‖f ((a : G) * g)‖ ≤ (nu Ξ σ (2 * t) f).toReal *
        ((C ^ 2) ^ t * (Ξ g * (1 + σ g) ^ (-r)) * (1 + σ a) ^ (-r₀)) := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
      calc Ξ g * (1 + σ ((a : G) * g)) ^ (-(2 * t))
          ≤ Ξ g * ((C ^ 2) ^ t * ((1 + σ g) ^ (-t) * (1 + σ a) ^ (-t))) :=
            mul_le_mul_of_nonneg_left hz (hw.pos g).le
        _ ≤ Ξ g * ((C ^ 2) ^ t * ((1 + σ g) ^ (-r) * (1 + σ a) ^ (-r₀))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCt) (hw.pos g).le
            exact mul_le_mul hxr hyr (Real.rpow_nonneg (by linarith) _)
              (Real.rpow_nonneg (by linarith) _)
        _ = (C ^ 2) ^ t * (Ξ g * (1 + σ g) ^ (-r)) * (1 + σ a) ^ (-r₀) := by ring
    rw [← ofReal_norm, ← ENNReal.ofReal_toReal hfs, mul_assoc (ENNReal.ofReal _),
      mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul hCt, ← ENNReal.ofReal_mul (mul_nonneg hCt hΞ),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (hreal.trans_eq (by ring))
  calc ‖centralProjection μA χ f g‖ₑ
      ≤ ∫⁻ a, ‖(((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g)‖ₑ ∂μA :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ a, ‖f ((a : G) * g)‖ₑ ∂μA :=
        lintegral_congr fun a => by rw [enorm_mul, hχ.enorm_inv, one_mul]
    _ ≤ ∫⁻ a, nu Ξ σ (2 * t) f * ENNReal.ofReal ((C ^ 2) ^ t) *
          ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) * ENNReal.ofReal ((1 + σ a) ^ (-r₀)) ∂μA :=
        lintegral_mono hpt
    _ = nu Ξ σ (2 * t) f * ENNReal.ofReal ((C ^ 2) ^ t) *
          ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) *
          ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-r₀)) ∂μA :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top hfs ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top)
    _ = _ := by ring

end CentralWeights

/-- `p_χ f` is `χ`-covariant: `(p_χ f)(b g) = χ(b) (p_χ f)(g)` for `b ∈ A`, when `μ_A` is right
invariant. -/
theorem centralProjection_mul_left [MeasurableMul A]
    [μA.IsMulRightInvariant] (f : G → ℂ) (b : A) (g : G) :
    centralProjection μA χ f ((b : G) * g) = χ b * centralProjection μA χ f g := by
  unfold centralProjection
  set φ : A → ℂ := fun a => (((χ (a * b⁻¹))⁻¹ : ℂˣ) : ℂ) * f (((a * b⁻¹ : A) : G) * ((b : G) * g))
  have hφ : ∀ a, φ (a * b) = (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * ((b : G) * g)) := fun a => by
    simp only [φ, mul_inv_cancel_right]
  have hφ' : ∀ a, φ a = (χ b : ℂ) * ((((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g)) := fun a => by
    have hχ : (χ (a * b⁻¹))⁻¹ = χ b * (χ a)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv]
    have hg : ((a * b⁻¹ : A) : G) * ((b : G) * g) = (a : G) * g := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    simp only [φ, hχ, hg, Units.val_mul, mul_assoc]
  calc ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * ((b : G) * g)) ∂μA
      = ∫ a, φ (a * b) ∂μA := by simp only [hφ]
    _ = ∫ a, φ a ∂μA := integral_mul_right_eq_self φ b
    _ = ∫ a, (χ b : ℂ) * ((((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g)) ∂μA := by simp only [hφ']
    _ = (χ b : ℂ) * ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g) ∂μA := integral_const_mul _ _

/-- For central `A`, `p_χ` preserves bi-invariance under any subgroup `H`. -/
theorem IsBiInvariant.centralProjection (hA : A ≤ Subgroup.center G) {H : Subgroup G}
    {f : G → ℂ} (hf : IsBiInvariant H f) (χ : A →* ℂˣ) :
    IsBiInvariant H (centralProjection μA χ f) := by
  intro h₁ h₁m h₂ h₂m g
  unfold HarishChandraSchwartz.centralProjection
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hc : h₁ * (a : G) = (a : G) * h₁ := Subgroup.mem_center_iff.mp (hA a.2) h₁
  have : (a : G) * (h₁ * g * h₂) = h₁ * ((a : G) * g) * h₂ := by
    rw [← mul_assoc, ← mul_assoc, ← hc, mul_assoc h₁]
  simp only [this, hf h₁ h₁m h₂ h₂m]

section Space

variable [TopologicalSpace G] [IsTopologicalGroup G] [OpensMeasurableSpace A]

namespace CentralWeights

/-- For `f ∈ C_H`, `a ↦ f(a g)` is integrable on `A`. -/
theorem integrable_of_mem_level (hw : CentralWeights μA Ξ σ) {H : CompactOpenSubgroup G}
    {f : G → ℂ} (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup) (g : G) :
    Integrable (fun a : A => f ((a : G) * g)) μA := by
  obtain ⟨s, hs, hI⟩ := hw.exists_lintegral_lt_top
  refine ⟨((continuous_of_mem_levelSubmodule hf).comp
    (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable, ?_⟩
  exact (hw.lintegral_enorm_le hs (hf.2 s).ne g).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (hf.2 s) ENNReal.ofReal_lt_top) hI)

/-- For `f ∈ C_H` and unitary `χ`, the integrand `a ↦ χ(a)⁻¹ f(a g)` of `p_χ f(g)` is
integrable: the integral defining `p_χ` converges absolutely. -/
theorem integrable_mul_of_mem_level (hw : CentralWeights μA Ξ σ) (hχ : IsUnitaryCharacter χ)
    {H : CompactOpenSubgroup G} {f : G → ℂ} (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup)
    (g : G) : Integrable (fun a : A => (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g)) μA :=
  (hw.integrable_of_mem_level hf g).bdd_mul hχ.measurable_inv.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => (hχ.norm_inv a).le)

variable [Nonempty (CompactOpenSubgroup G)]

/-- For `f ∈ C(G)` and unitary `χ`, the integrand of `p_χ f(g)` is integrable. -/
theorem integrable_mul_of_mem (hw : CentralWeights μA Ξ σ) (hχ : IsUnitaryCharacter χ)
    {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) (g : G) :
    Integrable (fun a : A => (((χ a)⁻¹ : ℂˣ) : ℂ) * f ((a : G) * g)) μA := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  exact hw.integrable_mul_of_mem_level hχ hH g

end CentralWeights

variable [Nonempty (CompactOpenSubgroup G)]

/-- Waldspurger's `p_χ` as a linear map from `C(G)` to functions on `G`. -/
def Space.centralProjection (hw : CentralWeights μA Ξ σ) (hχ : IsUnitaryCharacter χ) :
    Space Ξ σ →ₗ[ℂ] (G → ℂ) where
  toFun f := HarishChandraSchwartz.centralProjection μA χ f
  map_add' f₁ f₂ := by
    funext g
    simp only [HarishChandraSchwartz.centralProjection, Space.coe_add, Pi.add_apply, mul_add]
    exact integral_add (hw.integrable_mul_of_mem hχ (Space.coe_mem f₁) g)
      (hw.integrable_mul_of_mem hχ (Space.coe_mem f₂) g)
  map_smul' c f := by
    funext g
    simp only [HarishChandraSchwartz.centralProjection, Space.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext a
    ring

@[simp] theorem Space.centralProjection_apply (hw : CentralWeights μA Ξ σ)
    (hχ : IsUnitaryCharacter χ) (f : Space Ξ σ) :
    Space.centralProjection hw hχ f = HarishChandraSchwartz.centralProjection μA χ f :=
  rfl

end Space

end Weights

end Langlands.HarishChandraSchwartz
