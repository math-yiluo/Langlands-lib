import Langlands.LocalFactor.ArchimedeanPresentation
import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds
import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.LocalFactor.ArchimedeanScaling

/-!
# Rapidly decreasing Mellin pairs for the real pair factors

See the paired Markdown file.
-/

open MeasureTheory Set Filter Complex
open scoped Topology Real

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

open ArchimedeanMellinPair

/-- Generic pair construction. If `D`, `Dd`, `E` are entire of exponential type in vertical
strips and nonzero on a right half-plane, there are measurable rapidly decreasing `h`, `k`
with `mellin h (-s) = sign E(s) exp(s²) D(s)` and `mellin k (s - 1) = exp(s²) Dd(1 - s)`;
hence the factor identity `D(s)⁻¹ mellin h (-s) = sign E(s) Dd(1 - s)⁻¹ mellin k (s - 1)`
off a discrete set. -/
theorem exists_factor_pair {D Dd E : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hDd : Differentiable ℂ Dd) (hE : Differentiable ℂ E) (hDt : StripExpType D)
    (hDdt : StripExpType Dd) (hEt : StripExpType E) {sign : ℂ} (hsign : sign ≠ 0)
    {σ₀ : ℝ} (h0 : ∀ s : ℂ, σ₀ < s.re → D s ≠ 0 ∧ Dd s ≠ 0 ∧ E s ≠ 0) :
    ∃ h k : ℝ → ℂ, Measurable h ∧ Measurable k ∧ RapidDecay h ∧ RapidDecay k ∧
      (∀ s : ℂ, mellin h (-s) = sign * E s * Complex.exp (s ^ 2) * D s) ∧
      (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) * Dd (1 - s)) ∧
      (∀ s : ℂ, σ₀ < s.re → mellin h (-s) ≠ 0) ∧
      (∀ s : ℂ, σ₀ < s.re → mellin k (-s) ≠ 0) ∧
      ∀ᶠ s in codiscrete ℂ,
        (D s)⁻¹ * mellin h (-s) = sign * E s * (Dd (1 - s))⁻¹ * mellin k (s - 1) := by
  set mh : ℂ → ℂ := fun u => Complex.exp (u ^ 2) * (sign * E (-u) * D (-u)) with hmh
  set mk : ℂ → ℂ := fun u => Complex.exp ((u + 1) ^ 2) * Dd (-u) with hmk
  have hmh_diff : Differentiable ℂ mh := by
    have h1 : Differentiable ℂ (fun u : ℂ => Complex.exp (u ^ 2)) :=
      Complex.differentiable_exp.comp (differentiable_id.pow 2)
    exact h1.mul (((differentiable_const sign).mul (hE.comp differentiable_neg)).mul
      (hD.comp differentiable_neg))
  have hmk_diff : Differentiable ℂ mk := by
    have h1 : Differentiable ℂ (fun u : ℂ => Complex.exp ((u + 1) ^ 2)) :=
      Complex.differentiable_exp.comp ((differentiable_id.add_const 1).pow 2)
    exact h1.mul (hDd.comp differentiable_neg)
  have hmh_dec : StripDecay mh := by
    have : StripExpType (fun u => sign * E (-u) * D (-u)) := by
      refine (((StripExpType.const sign).mul (hEt.comp_ofReal_mul (-1))).mul
        (hDt.comp_ofReal_mul (-1))).congr fun u => ?_
      simp only [ofReal_neg, ofReal_one, neg_one_mul]
    exact stripDecay_exp_sq_mul this
  have hmk_dec : StripDecay mk := by
    have hF : StripExpType (fun v => Dd (1 - v)) := by
      refine ((hDdt.comp_ofReal_mul (-1)).comp_add (-1)).congr fun v => ?_
      congr 1
      push_cast
      ring
    refine ((stripDecay_exp_sq_mul hF).comp_add_ofReal 1).congr fun u => ?_
    simp only [hmk, ofReal_one]
    congr 2
    ring
  obtain ⟨h, hhm, hhd, hhM⟩ := exists_mellin_eq hmh_diff hmh_dec
  obtain ⟨k, hkm, hkd, hkM⟩ := exists_mellin_eq hmk_diff hmk_dec
  refine ⟨h, k, hhm, hkm, hhd, hkd, fun s => ?_, fun s => ?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · rw [hhM]
    simp only [hmh, neg_neg, neg_sq]
    ring
  · rw [hkM]
    simp only [hmk, show s - 1 + 1 = s by ring, show -(s - 1) = 1 - s by ring]
  · rw [hhM]
    simp only [hmh, neg_neg]
    obtain ⟨h1, -, h3⟩ := h0 s hs
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero hsign h3) h1)
  · rw [hkM]
    simp only [hmk, neg_neg]
    exact mul_ne_zero (Complex.exp_ne_zero _) (h0 s hs).2.1
  · have hA : AnalyticOnNhd ℂ D univ := fun z _ => hD.analyticAt z
    have hB : AnalyticOnNhd ℂ (fun s => Dd (1 - s)) univ := fun z _ =>
      (hDd.comp ((differentiable_const 1).sub differentiable_id)).analyticAt z
    have hA0 := hA.preimage_zero_mem_codiscrete (x := ((σ₀ + 1 : ℝ) : ℂ))
      (h0 _ (by simp)).1
    have hB0 := hB.preimage_zero_mem_codiscrete (x := ((-σ₀ : ℝ) : ℂ)) (by
      have := (h0 ((1 + σ₀ : ℝ) : ℂ) (by simp)).2.1
      convert this using 2
      push_cast
      ring)
    filter_upwards [hA0, hB0] with s h1 h2
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at h1 h2
    rw [hhM, hkM]
    simp only [hmh, hmk, neg_neg, show s - 1 + 1 = s by ring, show -(s - 1) = 1 - s by ring,
      neg_sq]
    field_simp

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.Archimedean ArchimedeanMellinPair ArchimedeanInverseMellin

namespace ArchimedeanRealPairFactor

theorem block_lFactor_stripExpType (x : RealBlock) : StripExpType x.lFactor.denominator := by
  cases x with
  | character d =>
    rw [RealBlock.lFactor_character]
    exact inv_Gammaℝ_stripExpType.comp_add _
  | induced d =>
    rw [RealBlock.lFactor_induced]
    exact inv_Gammaℂ_stripExpType.comp_add _

theorem realLFactor_stripExpType (xs : List RealBlock) :
    StripExpType (realLFactor xs).denominator := by
  refine (StripExpType.list_prod xs (fun x => x.lFactor.denominator)
    fun x _ => block_lFactor_stripExpType x).congr fun s => ?_
  rw [denominator_realLFactor]

theorem block_lFactor_ne_zero (x : RealBlock) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → x.lFactor.denominator s ≠ 0 := by
  cases x with
  | character d =>
    set e : ℂ := d.exponent + (d.parity.val : ℂ) with he
    refine ⟨-e.re, fun s hs => ?_⟩
    rw [RealBlock.lFactor_character]
    change (Complex.Gammaℝ (s + e))⁻¹ ≠ 0
    refine inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
    rw [Complex.add_re]
    linarith
  | induced d =>
    set e : ℂ := d.exponent + (d.weight.natAbs : ℂ) / 2 with he
    refine ⟨-e.re, fun s hs => ?_⟩
    rw [RealBlock.lFactor_induced]
    change (Complex.Gammaℂ (s + e))⁻¹ ≠ 0
    refine inv_ne_zero ?_
    have hre : 0 < (s + e).re := by rw [Complex.add_re]; linarith
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hre)
    exact Complex.cpow_ne_zero_iff.mpr (.inl (by
      exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)))

theorem realLFactor_ne_zero (xs : List RealBlock) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (realLFactor xs).denominator s ≠ 0 := by
  induction xs with
  | nil => exact ⟨0, fun s _ => by simp [LocalFactor.ReciprocalEntire.one]⟩
  | cons x xs ih =>
    obtain ⟨σ₁, h₁⟩ := block_lFactor_ne_zero x
    obtain ⟨σ₂, h₂⟩ := ih
    refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
    rw [denominator_realLFactor, List.map_cons, List.prod_cons, ← denominator_realLFactor]
    exact mul_ne_zero (h₁ s (lt_of_le_of_lt (le_max_left _ _) hs))
      (h₂ s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem block_epsilon_stripExpType (x : RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) :
    StripExpType (fun s => (x.epsilon a c hc s : ℂ)) := by
  have hr : 0 < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  cases x with
  | character d =>
    refine ((StripExpType.const ((c : ℂ) * (d.character a : ℂ))).mul
      (((StripExpType.ofReal_cpow hr).comp_add (-1)).mul
        (StripExpType.const (Complex.I ^ d.parity.val)))).congr fun s => ?_
    change _ = (d.epsilon a c hc s : ℂ)
    rw [RealCharacterData.coe_epsilon, sub_eq_add_neg]
    ring
  | induced d =>
    refine ((StripExpType.const ((c : ℂ) ^ 2 *
      ((((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (d.character (realToComplex a) : ℂ)))).mul
      ((((StripExpType.ofReal_cpow hr).comp_ofReal_mul 2).comp_add (-1)).mul
        (StripExpType.const (Complex.I ^ (d.weight.natAbs + 1))))).congr fun s => ?_
    change _ = (d.realInducedEpsilon a c hc s : ℂ)
    rw [ComplexCharacterData.coe_realInducedEpsilon]
    have : ((2 : ℝ) : ℂ) * (s + -1) = 2 * (s - 1) := by push_cast; ring
    rw [this]
    ring

theorem block_epsilon_differentiable (x : RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) :
    Differentiable ℂ (fun s => (x.epsilon a c hc s : ℂ)) :=
  x.differentiable_epsilon a c hc

theorem realEpsilon_stripExpType (xs : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) :
    StripExpType (fun s => (realEpsilon xs a c hc s : ℂ)) := by
  induction xs with
  | nil => exact (StripExpType.const 1).congr fun s => by simp [realEpsilon]
  | cons x xs ih =>
    exact ((block_epsilon_stripExpType x a c hc).mul ih).congr fun s => by simp [realEpsilon]

theorem realEpsilon_differentiable (xs : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) :
    Differentiable ℂ (fun s => (realEpsilon xs a c hc s : ℂ)) :=
  Langlands.LocalFactor.Archimedean.differentiable_realEpsilon xs a c hc

end ArchimedeanRealPairFactor

open ArchimedeanRealPairFactor

/-- Existence of rapidly decreasing Mellin pairs for the real pair factors: for block lists
`ds, es, dds, ees`, an epsilon parameter `b`, a positive scale `c` and a nonzero `sign`, there
are measurable rapidly decreasing `h`, `k` whose Mellin transforms are nonzero on a right
half-plane and satisfy, off a discrete set, the factor identity
`L(s) mellin h (-s) = sign ε(s) Ld(1 - s) mellin k (s - 1)` with
`L = (realPairLFactor ds es).denominator⁻¹`, `Ld = (realPairLFactor dds ees).denominator⁻¹` and
`ε = realPairEpsilon ds es b c`. -/
def RealPairMellinFactorStatement : Prop :=
  ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : NNReal) (hc : 0 < c) (sign : ℂ),
    sign ≠ 0 →
    ∃ (σ₁ : ℝ) (h k : ℝ → ℂ), Measurable h ∧ Measurable k ∧ RapidDecay h ∧ RapidDecay k ∧
      (∀ s : ℂ, mellin h (-s) = sign * (realPairEpsilon ds es b c hc s : ℂ) *
        Complex.exp (s ^ 2) * (realPairLFactor ds es).denominator s) ∧
      (∀ s : ℂ, mellin k (s - 1) =
        Complex.exp (s ^ 2) * (realPairLFactor dds ees).denominator (1 - s)) ∧
      (∀ s : ℂ, σ₁ < s.re → mellin h (-s) ≠ 0) ∧
      (∀ s : ℂ, σ₁ < s.re → mellin k (-s) ≠ 0) ∧
      ∀ᶠ s in codiscrete ℂ,
        ((realPairLFactor ds es).denominator s)⁻¹ * mellin h (-s) =
          sign * (realPairEpsilon ds es b c hc s : ℂ) *
            ((realPairLFactor dds ees).denominator (1 - s))⁻¹ * mellin k (s - 1)

theorem realPairMellinFactor : RealPairMellinFactorStatement := by
  intro ds es dds ees b c hc sign hsign
  obtain ⟨σa, ha⟩ := realLFactor_ne_zero (realPairBlocks ds es)
  obtain ⟨σb, hb⟩ := realLFactor_ne_zero (realPairBlocks dds ees)
  obtain ⟨h, k, hhm, hkm, hhd, hkd, hhf, hkf, hh0, hk0, hfac⟩ :=
    exists_factor_pair (D := (realPairLFactor ds es).denominator)
      (Dd := (realPairLFactor dds ees).denominator)
      (E := fun s => (realPairEpsilon ds es b c hc s : ℂ))
      (realPairLFactor ds es).entire (realPairLFactor dds ees).entire
      (realEpsilon_differentiable _ b c hc) (realLFactor_stripExpType _)
      (realLFactor_stripExpType _) (realEpsilon_stripExpType _ b c hc) hsign
      (σ₀ := max σa σb) fun s hs =>
        ⟨ha s (lt_of_le_of_lt (le_max_left _ _) hs),
          hb s (lt_of_le_of_lt (le_max_right _ _) hs), Units.ne_zero _⟩
  exact ⟨max σa σb, h, k, hhm, hkm, hhd, hkd, hhf, hkf, hh0, hk0, hfac⟩

end Langlands.Global.RankinSelbergGlobal
