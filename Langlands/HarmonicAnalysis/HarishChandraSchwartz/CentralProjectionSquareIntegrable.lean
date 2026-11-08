import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2

/-! # Square integrability of `p_χ f` on `A_G \ G` (Waldspurger VIII.4.1, VIII.4.2)

Waldspurger 2003, proof of Proposition VIII.4.1 (p. 328): for `f₁, f₂ ∈ p_χ(°C_H)` the integral
`(f₁, f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁(g)) f₂(g) dg` is absolutely convergent; proof of
Theorem VIII.4.2 (p. 331): the coefficient `(f₁, ρ(g) f₂)_{A_G\G} = p_χ(φ̌̄₁ ∗ φ₂)(g)` "est de
carré intégrable sur `A_G \ G`".

This module proves, for abstract data, that `p_χ f` is square integrable on `A \ G` for every
`f ∈ C(G)`: with `Φ(g) = ∫_A |f(a g)| da` (`centralAbsIntegral`), `|p_χ f| ≤ Φ`, `Φ` is
`A`-invariant, and the Weil formula gives `∫_{A\G} Φ² = ∫_G |f| Φ`, which is finite by the
bounds `|f| ≤ ν_{s+d}(f) Ξ (1 + σ)^{-s-d}`, `Φ ≤ c Ξ (1 + σ)^s` and `∫_G Ξ² (1 + σ)^{-d} < ∞`.

* `lintegral_lintegral_out_eq`: the Weil formula for nonnegative measurable functions;
* `lintegral_enorm_centralProjection_out_sq_lt_top`: `∫_{A\G} |p_χ f|² < ∞`;
* `exists_memLp_two_centralProjection`: `|p_χ f|` descends to an `L²` function on `A \ G`;
* `integrable_centralProjection_mul_conj_out`: the product `(p_χ f₁, p_χ f₂)_{A\G}` converges
  absolutely.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

section Absolute

variable {G : Type u} [Group G] {A : Subgroup G} [MeasurableSpace A]

/-- `Φ(g) = ∫_A |f(a g)| dμ_A(a)`, the absolute value integral that bounds `|p_χ f(g)|`. -/
def centralAbsIntegral (μA : Measure A) (f : G → ℂ) (g : G) : ℝ≥0∞ :=
  ∫⁻ a, ‖f ((a : G) * g)‖ₑ ∂μA

variable {μA : Measure A} {χ : A →* ℂˣ}

/-- `|p_χ f(g)| ≤ Φ(g)` for a unitary `χ`. -/
theorem enorm_centralProjection_le_centralAbsIntegral (hχ : IsUnitaryCharacter χ)
    (f : G → ℂ) (g : G) : ‖centralProjection μA χ f g‖ₑ ≤ centralAbsIntegral μA f g := by
  refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun a => ?_)
  rw [enorm_mul, hχ.enorm_inv, one_mul]

/-- `Φ` is invariant under `A`: `Φ(b g) = Φ(g)` for `b ∈ A`, when `μ_A` is right invariant. -/
theorem centralAbsIntegral_mul_left [MeasurableMul A] [μA.IsMulRightInvariant] (f : G → ℂ)
    (b : A) (g : G) : centralAbsIntegral μA f ((b : G) * g) = centralAbsIntegral μA f g := by
  unfold centralAbsIntegral
  have h := lintegral_mul_right_eq_self (μ := μA) (fun a : A => ‖f ((a : G) * g)‖ₑ) b
  simpa only [Subgroup.coe_mul, mul_assoc] using h

end Absolute

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {Ξ σ : G → ℝ} {χ : A →* ℂˣ}

include hA in
/-- **Weil formula** for nonnegative measurable functions, read through representatives:
`∫_{A\G} ∫_A F(a q̇) dμ_A(a) dν(q) = ∫_G F dμ_G`, where `q̇ = Quotient.out q`. -/
theorem lintegral_lintegral_out_eq (hν : IsCompatible A μG μA ν) {F : G → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ q, ∫⁻ a, F ((a : G) * q.out) ∂μA ∂ν = ∫⁻ g, F g ∂μG := by
  rw [← lintegral_orbitKernel A hA μA μG ν hν F hF]
  refine lintegral_congr fun q => ?_
  have hq' : orbitKernel A hA μA q = Measure.map (fun a : A => (a : G) * q.out) μA := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hm : Measurable fun a : A => (a : G) * q.out :=
    (continuous_subtype_val.mul continuous_const).measurable
  rw [hq', lintegral_map hF hm]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)] in
/-- A continuous `A`-invariant function read through the representatives `q̇` is continuous
on `A \ G`. -/
theorem continuous_out_of_invariant {X : Type*} [TopologicalSpace X] {P : G → X}
    (hP : Continuous P) (hinv : ∀ (b : A) (g : G), P ((b : G) * g) = P g) :
    Continuous fun q : LeftQuotient A => P q.out := by
  have h : (fun q : LeftQuotient A => P q.out) = descend A P hinv := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  rw [h]
  exact hP.quotient_lift _

include hA in
/-- **`p_χ f` is square integrable on `A \ G`**: for a measurable `f` with all `ν_r(f)`
finite, `∫_{A\G} |p_χ f(q̇)|² dν(q) < ∞`. -/
theorem lintegral_enorm_centralProjection_out_sq_lt_top [MeasurableMul A]
    (hν : IsCompatible A μG μA ν) (hw : CentralWeights μA Ξ σ) (hL : L2Weights μG Ξ σ)
    (hχ : IsUnitaryCharacter χ) {f : G → ℂ} (hfm : Measurable f) (hf : ∀ r, nu Ξ σ r f < ⊤) :
    ∫⁻ q, ‖centralProjection μA χ f q.out‖ₑ ^ 2 ∂ν < ⊤ := by
  obtain ⟨s, hs, hI⟩ := hw.exists_lintegral_lt_top
  obtain ⟨d, hd⟩ := hL.square
  set I := ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA with hIdef
  set C := nu Ξ σ (s + d) f * nu Ξ σ s f * I with hCdef
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (hf _).ne (hf _).ne) hI.ne
  have hfA : ∀ g : G, Measurable fun a : A => ‖f ((a : G) * g)‖ₑ := fun g =>
    (hfm.comp (continuous_subtype_val.mul continuous_const).measurable).enorm
  have hΦm : Measurable (centralAbsIntegral μA f) := by
    have h : Measurable fun p : G × A => ‖f ((p.2 : G) * p.1)‖ₑ :=
      (hfm.comp ((continuous_subtype_val.comp continuous_snd).mul
        continuous_fst).measurable).enorm
    exact h.lintegral_prod_right'
  have hpt : ∀ g : G, ‖f g‖ₑ * centralAbsIntegral μA f g ≤
      C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
    intro g
    have hb : 0 < 1 + σ g := by linarith [hw.nonneg g]
    have h1 : ‖f g‖ₑ ≤ nu Ξ σ (s + d) f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d))) := by
      have h := norm_le_of_nu hw.pos hw.nonneg (hf (s + d)).ne g
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal (hf (s + d)).ne,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal h
    have h2 := hw.lintegral_enorm_le hs (hf s).ne g
    have hx : 0 ≤ Ξ g * (1 + σ g) ^ (-(s + d)) :=
      mul_nonneg (hw.pos g).le (Real.rpow_nonneg hb.le _)
    have hreal : Ξ g * (1 + σ g) ^ (-(s + d)) * (Ξ g * (1 + σ g) ^ s) =
        Ξ g ^ 2 * (1 + σ g) ^ (-d) := by
      rw [show Ξ g * (1 + σ g) ^ (-(s + d)) * (Ξ g * (1 + σ g) ^ s) =
          Ξ g ^ 2 * ((1 + σ g) ^ (-(s + d)) * (1 + σ g) ^ s) by ring, ← Real.rpow_add hb]
      congr 2
      ring
    calc ‖f g‖ₑ * centralAbsIntegral μA f g
        ≤ (nu Ξ σ (s + d) f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d)))) *
            (nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) * I) := mul_le_mul' h1 h2
      _ = C * (ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d))) *
            ENNReal.ofReal (Ξ g * (1 + σ g) ^ s)) := by rw [hCdef]; ring
      _ = C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
          rw [← ENNReal.ofReal_mul hx, hreal]
  calc ∫⁻ q, ‖centralProjection μA χ f q.out‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ q, centralAbsIntegral μA f q.out ^ 2 ∂ν :=
        lintegral_mono fun q =>
          pow_le_pow_left' (enorm_centralProjection_le_centralAbsIntegral hχ f q.out) 2
    _ = ∫⁻ q, ∫⁻ a, (fun g => ‖f g‖ₑ * centralAbsIntegral μA f g) ((a : G) * q.out) ∂μA ∂ν := by
        refine lintegral_congr fun q => ?_
        simp only [centralAbsIntegral_mul_left]
        rw [lintegral_mul_const _ (hfA q.out), sq]
        rfl
    _ = ∫⁻ g, ‖f g‖ₑ * centralAbsIntegral μA f g ∂μG :=
        lintegral_lintegral_out_eq hA hν (hfm.enorm.mul hΦm)
    _ ≤ ∫⁻ g, C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μG := lintegral_mono hpt
    _ = C * ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μG := lintegral_const_mul' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hd

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)] [SFinite μA]
  [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA] [BorelSpace A]
  [IsFiniteMeasureOnCompacts μG] in
/-- For `f ∈ C_H`, central `A` and unitary `χ`, `p_χ f` is continuous and `‖p_χ f‖` is
`A`-invariant. -/
theorem continuous_centralProjection (hAc : A ≤ Subgroup.center G)
    {H : CompactOpenSubgroup G} {f : G → ℂ} (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup) :
    Continuous (centralProjection μA χ f) :=
  (IsBiInvariant.isLocallyConstant (K := H) (hf.1.centralProjection hAc χ)).continuous

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace (LeftQuotient A)]
  [BorelSpace (LeftQuotient A)] [SFinite μA] [IsFiniteMeasureOnCompacts μA] [BorelSpace A]
  [IsFiniteMeasureOnCompacts μG] in
/-- `|p_χ f|` is `A`-invariant for unitary `χ`. -/
theorem norm_centralProjection_mul_left [MeasurableMul A] (hχ : IsUnitaryCharacter χ)
    (f : G → ℂ) (b : A) (g : G) :
    ‖centralProjection μA χ f ((b : G) * g)‖ = ‖centralProjection μA χ f g‖ := by
  rw [centralProjection_mul_left, norm_mul, hχ.norm_eq_one, one_mul]

include hA in
/-- **`p_χ f ∈ L²(A \ G)`** for `f ∈ C(G)`: `|p_χ f|` descends to a function on `A \ G` in
`L²(ν)`. -/
theorem exists_memLp_two_centralProjection [MeasurableMul A] [Nonempty (CompactOpenSubgroup G)]
    (hν : IsCompatible A μG μA ν) (hAc : A ≤ Subgroup.center G) (hw : CentralWeights μA Ξ σ)
    (hL : L2Weights μG Ξ σ) (hχ : IsUnitaryCharacter χ) {f : G → ℂ}
    (hf : f ∈ schwartzSubmodule Ξ σ) :
    ∃ F : LeftQuotient A → ℝ, MemLp F 2 ν ∧
      ∀ g : G, F (Quotient.mk _ g) = ‖centralProjection μA χ f g‖ := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  have hinv : ∀ (b : A) (g : G), ‖centralProjection μA χ f ((b : G) * g)‖ =
      ‖centralProjection μA χ f g‖ := norm_centralProjection_mul_left hχ f
  have hcont : Continuous fun g => ‖centralProjection μA χ f g‖ :=
    (continuous_centralProjection hAc hH).norm
  refine ⟨descend A (fun g => ‖centralProjection μA χ f g‖) hinv, ?_, fun g => rfl⟩
  have hdesc : descend A (fun g => ‖centralProjection μA χ f g‖) hinv =
      fun q : LeftQuotient A => ‖centralProjection μA χ f q.out‖ := by
    funext q
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hdesc]
  have hc : Continuous fun q : LeftQuotient A => ‖centralProjection μA χ f q.out‖ :=
    continuous_out_of_invariant hcont hinv
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hc.aestronglyMeasurable]
  simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact lintegral_enorm_centralProjection_out_sq_lt_top hA hν hw hL hχ
    (continuous_of_mem_levelSubmodule hH).measurable hH.2

include hA in
/-- **The product `(p_χ f₂, p_χ f₁)_{A\G}` converges absolutely** (proof of Proposition
VIII.4.1): for `f₁, f₂ ∈ C(G)`, central `A` and unitary `χ`,
`q ↦ p_χ f₁(q̇) conj(p_χ f₂(q̇))` is integrable on `A \ G`. -/
theorem integrable_centralProjection_mul_conj_out [MeasurableMul A]
    [Nonempty (CompactOpenSubgroup G)] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hw : CentralWeights μA Ξ σ) (hL : L2Weights μG Ξ σ)
    (hχ : IsUnitaryCharacter χ) {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ schwartzSubmodule Ξ σ)
    (h₂ : f₂ ∈ schwartzSubmodule Ξ σ) :
    Integrable (fun q : LeftQuotient A =>
      centralProjection μA χ f₁ q.out * conj (centralProjection μA χ f₂ q.out)) ν := by
  obtain ⟨H₁, hH₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₁
  obtain ⟨H₂, hH₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₂
  have hc₁ := continuous_centralProjection (μA := μA) (χ := χ) hAc hH₁
  have hc₂ := continuous_centralProjection (μA := μA) (χ := χ) hAc hH₂
  have hinvP : ∀ (b : A) (g : G),
      centralProjection μA χ f₁ ((b : G) * g) * conj (centralProjection μA χ f₂ ((b : G) * g)) =
        centralProjection μA χ f₁ g * conj (centralProjection μA χ f₂ g) := by
    intro b g
    rw [centralProjection_mul_left, centralProjection_mul_left, map_mul]
    have hb : (χ b : ℂ) * conj (χ b : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_eq_one]
      norm_num
    calc (χ b : ℂ) * centralProjection μA χ f₁ g *
          (conj (χ b : ℂ) * conj (centralProjection μA χ f₂ g))
        = ((χ b : ℂ) * conj (χ b : ℂ)) *
            (centralProjection μA χ f₁ g * conj (centralProjection μA χ f₂ g)) := by ring
      _ = _ := by rw [hb, one_mul]
  have hP : Continuous fun q : LeftQuotient A =>
      centralProjection μA χ f₁ q.out * conj (centralProjection μA χ f₂ q.out) :=
    continuous_out_of_invariant (hc₁.mul (Complex.continuous_conj.comp hc₂)) hinvP
  have hE : ∀ {f : G → ℂ} {H : CompactOpenSubgroup G}, f ∈ levelSubmodule Ξ σ H.toSubgroup →
      Measurable fun q : LeftQuotient A => ‖centralProjection μA χ f q.out‖ₑ ^ 2 := by
    intro f H hH
    have hcont : Continuous fun q : LeftQuotient A => ‖centralProjection μA χ f q.out‖ₑ := by
      have h := continuous_out_of_invariant (A := A)
        (continuous_enorm.comp (continuous_centralProjection (μA := μA) (χ := χ) hAc hH))
        (fun b g => by
          simp only [Function.comp_apply]
          rw [← ofReal_norm, ← ofReal_norm, norm_centralProjection_mul_left hχ])
      exact h
    exact hcont.measurable.pow_const 2
  refine ⟨hP.aestronglyMeasurable, ?_⟩
  have hfin₁ := lintegral_enorm_centralProjection_out_sq_lt_top hA hν hw hL hχ
    (continuous_of_mem_levelSubmodule hH₁).measurable hH₁.2
  have hfin₂ := lintegral_enorm_centralProjection_out_sq_lt_top hA hν hw hL hχ
    (continuous_of_mem_levelSubmodule hH₂).measurable hH₂.2
  unfold HasFiniteIntegral
  calc ∫⁻ q, ‖centralProjection μA χ f₁ q.out * conj (centralProjection μA χ f₂ q.out)‖ₑ ∂ν
      ≤ ∫⁻ q, (‖centralProjection μA χ f₁ q.out‖ₑ ^ 2 +
          ‖centralProjection μA χ f₂ q.out‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun q => ?_
        rw [enorm_mul, RCLike.enorm_conj]
        set x := ‖centralProjection μA χ f₁ q.out‖ₑ
        set y := ‖centralProjection μA χ f₂ q.out‖ₑ
        rcases le_total x y with hxy | hxy
        · calc x * y ≤ y * y := mul_le_mul' hxy le_rfl
            _ = y ^ 2 := (sq y).symm
            _ ≤ x ^ 2 + y ^ 2 := le_add_self
        · calc x * y ≤ x * x := mul_le_mul' le_rfl hxy
            _ = x ^ 2 := (sq x).symm
            _ ≤ x ^ 2 + y ^ 2 := le_self_add
    _ = ∫⁻ q, ‖centralProjection μA χ f₁ q.out‖ₑ ^ 2 ∂ν +
          ∫⁻ q, ‖centralProjection μA χ f₂ q.out‖ₑ ^ 2 ∂ν := lintegral_add_left (hE hH₁) _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin₁, hfin₂⟩

end Quotient

end Langlands.HarishChandraSchwartz
