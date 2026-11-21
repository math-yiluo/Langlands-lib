import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Mathlib.Order.Filter.Germ.Basic

/-! # Combining nonzero equal-rank local test integrals -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

namespace EqualLocalCommonTest

private abbrev integralFilter : Filter ℂ := comap Complex.re atTop

private abbrev IntegralGerm := Germ integralFilter ℂ

private theorem eventually_re_gt (σ : ℝ) : ∀ᶠ s in integralFilter, σ < Complex.re s :=
  (eventually_comap).2 ((eventually_gt_atTop σ).mono fun _ hb _ hs => hs ▸ hb)

private theorem germ_ne_zero_iff (f : ℂ → ℂ) :
    (f : IntegralGerm) ≠ 0 ↔ ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ f s ≠ 0 := by
  constructor
  · intro hf σ
    by_contra! h
    apply hf
    exact Germ.coe_eq.mpr ((eventually_re_gt σ).mono fun _ hs => h _ hs)
  · intro hf h
    have heq : f =ᶠ[integralFilter] (0 : ℂ → ℂ) := Germ.coe_eq.mp h
    obtain ⟨σ, hσ⟩ := eventually_atTop.mp (eventually_comap.mp heq)
    obtain ⟨s, hs, hn⟩ := hf σ
    exact hn (hσ s.re hs.le s rfl)

private theorem exists_common_ne_zero_of_add {A : Type*} [Add A]
    (I J : A → IntegralGerm)
    (hI : ∀ x y, I (x + y) = I x + I y) (hJ : ∀ x y, J (x + y) = J x + J y)
    {a b : A} (ha : I a ≠ 0) (hb : J b ≠ 0) :
    ∃ x, I x ≠ 0 ∧ J x ≠ 0 := by
  classical
  by_cases hJa : J a = 0
  · by_cases hIb : I b = 0
    · exact ⟨a + b, by simpa only [hI, hIb, add_zero] using ha,
        by simpa only [hJ, hJa, zero_add] using hb⟩
    · exact ⟨b, hIb, hb⟩
  · exact ⟨a, ha, hJa⟩

private theorem integralGerm_add {A Q : Type*} [Add A] [MeasurableSpace Q]
    (μ : Measure Q) (K : A → ℂ → Q → ℂ)
    (hAdd : ∀ x y s, K (x + y) s = K x s + K y s)
    (hInt : ∀ x, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (K x s) μ)
    (x y : A) :
    ((fun s => ∫ q, K (x + y) s q ∂μ) : IntegralGerm) =
      ((fun s => ∫ q, K x s q ∂μ) : IntegralGerm) +
      ((fun s => ∫ q, K y s q ∂μ) : IntegralGerm) := by
  obtain ⟨σ, hx⟩ := hInt x
  obtain ⟨τ, hy⟩ := hInt y
  rw [← Germ.coe_add]
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_re_gt σ, eventually_re_gt τ] with s hs ht
  simpa only [Pi.add_apply, hAdd x y s] using integral_add (hx s hs) (hy s ht)

variable {K : Type*} [Field K] [TopologicalSpace K] {r : ℕ}
  [MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient r K)]

local notation "G" => Langlands.GeneralLinear (r + 1) K
local notation "E" => Fin (r + 1) → K
local notation "Q" => Langlands.RankinSelberg.LeftUnipotentQuotient r K

/-- Separate ordinary and dual nonzero witnesses for the same measure give a common
triple. The maps with index `false` are the ordinary test maps and those with index `true`
incorporate the dual and Fourier operators. -/
theorem exists_common_nonzero {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]
    (nabs : K → ℝ) (μ : Measure Q)
    (W : Bool → A →+ (G → ℂ)) (V : Bool → B →+ (G → ℂ))
    (Φ : Bool → C →+ (E → ℂ))
    (hInt : ∀ i x y z, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (equalIntegrand nabs (W i x) (V i y) (Φ i z) s) μ)
    (hNonzero : ∀ i, ∃ x y z, ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
      equalIntegral nabs μ (W i x) (V i y) (Φ i z) s ≠ 0) :
    ∃ x y z, ∀ i (σ : ℝ), ∃ s : ℂ, σ < s.re ∧
      equalIntegral nabs μ (W i x) (V i y) (Φ i z) s ≠ 0 := by
  let I (i : Bool) (x : A) (y : B) (z : C) : IntegralGerm :=
    (equalIntegral nabs μ (W i x) (V i y) (Φ i z) : ℂ → ℂ)
  have hA i (y : B) (z : C) (x x' : A) :
      I i (x + x') y z = I i x y z + I i x' y z :=
    integralGerm_add μ (fun a => equalIntegrand nabs (W i a) (V i y) (Φ i z))
      (fun a b s => funext fun q => by
        simp only [equalIntegrand, map_add, Pi.add_apply, add_mul]) (fun a => hInt i a y z) x x'
  have hB i (x : A) (z : C) (y y' : B) :
      I i x (y + y') z = I i x y z + I i x y' z :=
    integralGerm_add μ (fun b => equalIntegrand nabs (W i x) (V i b) (Φ i z))
      (fun a b s => funext fun q => by
        simp only [equalIntegrand, map_add, Pi.add_apply, mul_add, add_mul])
      (fun b => hInt i x b z) y y'
  have hC i (x : A) (y : B) (z z' : C) :
      I i x y (z + z') = I i x y z + I i x y z' :=
    integralGerm_add μ (fun c => equalIntegrand nabs (W i x) (V i y) (Φ i c))
      (fun a b s => funext fun q => by
        simp only [equalIntegrand, map_add, Pi.add_apply, mul_add, add_mul])
      (fun c => hInt i x y c) z z'
  obtain ⟨x₀, y₀, z₀, h₀⟩ := hNonzero false
  obtain ⟨x₁, y₁, z₁, h₁⟩ := hNonzero true
  obtain ⟨x, hx₀, hx₁⟩ := exists_common_ne_zero_of_add
    (fun x => I false x y₀ z₀) (fun x => I true x y₁ z₁)
    (hA false y₀ z₀) (hA true y₁ z₁) ((germ_ne_zero_iff _).mpr h₀) ((germ_ne_zero_iff _).mpr h₁)
  obtain ⟨y, hy₀, hy₁⟩ := exists_common_ne_zero_of_add
    (fun y => I false x y z₀) (fun y => I true x y z₁)
    (hB false x z₀) (hB true x z₁) hx₀ hx₁
  obtain ⟨z, hz₀, hz₁⟩ := exists_common_ne_zero_of_add
    (fun z => I false x y z) (fun z => I true x y z)
    (hC false x y) (hC true x y) hy₀ hy₁
  refine ⟨x, y, z, fun i => ?_⟩
  cases i
  · exact (germ_ne_zero_iff _).mp hz₀
  · exact (germ_ne_zero_iff _).mp hz₁

end EqualLocalCommonTest

end Langlands.Global.RankinSelbergGlobal
