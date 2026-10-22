import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Order.Filter.Germ.Basic

/-! Reciprocals of nonzero entire functions, retaining their singular germs. -/

noncomputable section

open Filter Set
open scoped Topology

namespace Langlands.LocalFactor

/-- An entire denominator which is not identically zero. Its reciprocal is
represented by punctured germs, with numerical evaluation only at regular points. -/
structure ReciprocalEntire where
  denominator : ℂ → ℂ
  entire : Differentiable ℂ denominator
  nonzero : ∃ z, denominator z ≠ 0

namespace ReciprocalEntire

@[ext]
theorem ext {F G : ReciprocalEntire} (h : F.denominator = G.denominator) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The punctured meromorphic germ; the representative's value at the center
has no mathematical significance. -/
def germ (F : ReciprocalEntire) (z : ℂ) : Germ (𝓝[≠] z) ℂ :=
  Germ.ofFun (fun w => (F.denominator w)⁻¹)

theorem germ_meromorphic (F : ReciprocalEntire) (z : ℂ) :
    ∃ f : ℂ → ℂ, MeromorphicAt f z ∧ Germ.ofFun f = F.germ z :=
  ⟨_, (F.entire.analyticAt z).meromorphicAt.inv, rfl⟩

/-- Regular inputs of the reciprocal; zeros of the denominator are excluded. -/
def RegularPoint (F : ReciprocalEntire) := {z : ℂ // F.denominator z ≠ 0}

/-- Evaluation as a complex unit is available only on the regular domain. -/
def eval (F : ReciprocalEntire) (z : F.RegularPoint) : ℂˣ :=
  Units.mk0 (F.denominator z.val)⁻¹ (inv_ne_zero z.property)

@[simp]
theorem coe_eval (F : ReciprocalEntire) (z : F.RegularPoint) :
    (F.eval z : ℂ) = (F.denominator z.val)⁻¹ := rfl

/-- Zeros of the entire denominator. The theorem below proves that these are
precisely the points where the reciprocal germ has no analytic representative. -/
def IsPole (F : ReciprocalEntire) (z : ℂ) : Prop := F.denominator z = 0

theorem denominator_eventually_ne_zero (F : ReciprocalEntire) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, F.denominator w ≠ 0 := by
  rcases (F.entire.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have hf : AnalyticOnNhd ℂ F.denominator univ := fun w _ => F.entire.analyticAt w
    have hall : EqOn F.denominator 0 univ :=
      hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ z)
        (h.filter_mono nhdsWithin_le_nhds).frequently
    obtain ⟨w, hw⟩ := F.nonzero
    exact False.elim (hw (hall (mem_univ w)))
  · exact h

/-- This representation retains genuine poles: no analytic function can
represent the same punctured germ at a denominator zero. -/
theorem isPole_iff_no_analytic_germ (F : ReciprocalEntire) (z : ℂ) :
    F.IsPole z ↔
      ¬∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧ Germ.ofFun f = F.germ z := by
  constructor
  · intro hz ⟨f, hf, heq⟩
    have heq' : f =ᶠ[𝓝[≠] z] (fun w => (F.denominator w)⁻¹) :=
      Germ.coe_eq.mp heq
    have hprod : (fun w => F.denominator w * f w) =ᶠ[𝓝[≠] z] (fun _ => 1) := by
      filter_upwards [heq', F.denominator_eventually_ne_zero z] with w hw hden
      rw [hw, mul_inv_cancel₀ hden]
    have hlim : Tendsto (fun w => F.denominator w * f w) (𝓝[≠] z)
        (𝓝 (F.denominator z * f z)) :=
      (F.entire.continuous.continuousAt.mul hf.continuousAt).mono_left nhdsWithin_le_nhds
    have hone : Tendsto (fun w => F.denominator w * f w) (𝓝[≠] z) (𝓝 1) :=
      (tendsto_congr' hprod).mpr tendsto_const_nhds
    have h := tendsto_nhds_unique hlim hone
    have hz' : F.denominator z = 0 := hz
    simp only [hz', zero_mul] at h
    exact zero_ne_one h
  · intro h
    by_contra hz
    exact h ⟨_, (F.entire.analyticAt z).inv hz, rfl⟩

/-- The constant reciprocal one. -/
def one : ReciprocalEntire where
  denominator := fun _ => 1
  entire := differentiable_const _
  nonzero := ⟨0, one_ne_zero⟩

/-- Multiplication of reciprocals multiplies their entire denominators. -/
def mul (F G : ReciprocalEntire) : ReciprocalEntire where
  denominator := fun z => F.denominator z * G.denominator z
  entire := F.entire.mul G.entire
  nonzero := by
    by_contra h
    push Not at h
    have hf : AnalyticOnNhd ℂ F.denominator univ := fun z _ => F.entire.analyticAt z
    have hg : AnalyticOnNhd ℂ G.denominator univ := fun z _ => G.entire.analyticAt z
    rcases hf.eq_zero_or_eq_zero_of_mul_eq_zero hg (fun z _ => h z)
      isPreconnected_univ with hF | hG
    · obtain ⟨z, hz⟩ := F.nonzero
      exact hz (hF z (mem_univ z))
    · obtain ⟨z, hz⟩ := G.nonzero
      exact hz (hG z (mem_univ z))

@[simp]
theorem denominator_mul (F G : ReciprocalEntire) (z : ℂ) :
    (F.mul G).denominator z = F.denominator z * G.denominator z := rfl

theorem germ_mul (F G : ReciprocalEntire) (z : ℂ) :
    (F.mul G).germ z = F.germ z * G.germ z := by
  change Germ.ofFun (fun w => (F.denominator w * G.denominator w)⁻¹) =
    Germ.ofFun (fun w => (F.denominator w)⁻¹ * (G.denominator w)⁻¹)
  congr 1
  funext w
  exact mul_inv _ _

theorem isPole_mul (F G : ReciprocalEntire) (z : ℂ) :
    (F.mul G).IsPole z ↔ F.IsPole z ∨ G.IsPole z := mul_eq_zero

/-- Translation in the spectral variable. -/
def shift (F : ReciprocalEntire) (a : ℂ) : ReciprocalEntire where
  denominator := fun z => F.denominator (z + a)
  entire := F.entire.comp (differentiable_id.add_const a)
  nonzero := by
    obtain ⟨z, hz⟩ := F.nonzero
    exact ⟨z - a, by simpa using hz⟩

@[simp]
theorem denominator_shift (F : ReciprocalEntire) (a z : ℂ) :
    (F.shift a).denominator z = F.denominator (z + a) := rfl

/-- A finite list product, including the empty product. -/
def product : List ReciprocalEntire → ReciprocalEntire
  | [] => one
  | F :: Fs => F.mul (product Fs)

theorem denominator_product (Fs : List ReciprocalEntire) (z : ℂ) :
    (product Fs).denominator z = (Fs.map (fun F => F.denominator z)).prod := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp only [product, denominator_mul, List.map_cons, List.prod_cons, ih]

theorem product_perm {Fs Gs : List ReciprocalEntire} (h : Fs.Perm Gs) :
    product Fs = product Gs := by
  apply ext
  funext z
  rw [denominator_product, denominator_product]
  exact (h.map (fun F => F.denominator z)).prod_eq

theorem isPole_product (Fs : List ReciprocalEntire) (z : ℂ) :
    (product Fs).IsPole z ↔ ∃ F ∈ Fs, F.IsPole z := by
  induction Fs with
  | nil => simp [product, IsPole, one]
  | cons F Fs ih => simp [product, isPole_mul, ih]

end ReciprocalEntire
end Langlands.LocalFactor
