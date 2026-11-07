import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Exponential parameters of continuous archimedean characters -/

noncomputable section

open Topology

namespace Langlands.HarmonicAnalysis

/-- A continuous multiplicative function on the additive real line is an exponential. -/
theorem exists_exp_mul_of_continuous_add
    (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) (hne : ∀ x, f x ≠ 0) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) := by
  let F : C(ℝ, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨f x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, hg, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0
    (by apply Subtype.ext; simpa [F] using h0.symm)
  have hg0 : g 0 = 0 := hg.1
  have hgexp (x : ℝ) : Complex.exp (g x) = f x :=
    congrArg Subtype.val (congrFun hg.2 x)
  have hadd (x y : ℝ) : g (x + y) = g x + g y := by
    have he : (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
        (fun p : ℝ × ℝ => g (p.1 + p.2)) =
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
        (fun p : ℝ × ℝ => g p.1 + g p.2) := by
      funext p
      apply Subtype.ext
      simp only [Function.comp_apply, Complex.exp_add, hgexp, ha]
    have h := Complex.isCoveringMap_exp.eq_of_comp_eq
      (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))
      he (0, 0) (by simp [hg0])
    exact congrFun h (x, y)
  let L : ℝ →+ ℂ := AddMonoidHom.mk' g hadd
  refine ⟨g 1, fun x => ?_⟩
  have hx : g x = (x : ℂ) * g 1 := by
    simpa [L] using map_real_smul L g.continuous x 1
  rw [← hgexp, hx, mul_comm]

/-- A continuous circle-valued character on the real line has a real frequency. -/
theorem exists_circle_exp_mul_of_continuous_add
    (f : ℝ → Circle) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℝ, ∀ x : ℝ, f x = Circle.exp (c * x) := by
  let F : C(ℝ, Circle) := ⟨f, hc⟩
  obtain ⟨g, hg, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0
    (by simpa [F] using h0.symm)
  have hg0 : g 0 = 0 := hg.1
  have hgexp (x : ℝ) : Circle.exp (g x) = f x := congrFun hg.2 x
  have hadd (x y : ℝ) : g (x + y) = g x + g y := by
    have he : Circle.exp ∘ (fun p : ℝ × ℝ => g (p.1 + p.2)) =
        Circle.exp ∘ (fun p : ℝ × ℝ => g p.1 + g p.2) := by
      funext p
      simp only [Function.comp_apply, Circle.exp_add, hgexp, ha]
    have h := Circle.isCoveringMap_exp.eq_of_comp_eq
      (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))
      he (0, 0) (by simp [hg0])
    exact congrFun h (x, y)
  let L : ℝ →+ ℝ := AddMonoidHom.mk' g hadd
  refine ⟨g 1, fun x => ?_⟩
  have hx : g x = x * g 1 := by
    simpa [L] using map_real_smul L g.continuous x 1
  rw [← hgexp, hx, mul_comm]

/-- A continuous circle-valued character on the complex plane is a real linear phase. -/
theorem exists_circle_exp_re_im_of_continuous_add
    (f : ℂ → Circle) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) :
    ∃ a b : ℝ, ∀ z : ℂ, f z = Circle.exp (a * z.re + b * z.im) := by
  obtain ⟨a, ha'⟩ := exists_circle_exp_mul_of_continuous_add
    (fun x : ℝ => f x) (hc.comp Complex.continuous_ofReal) (by simpa using h0)
    (by intro x y; simpa using ha (x : ℂ) (y : ℂ))
  obtain ⟨b, hb'⟩ := exists_circle_exp_mul_of_continuous_add
    (fun x : ℝ => f ((x : ℂ) * Complex.I))
    (hc.comp (Complex.continuous_ofReal.mul_const Complex.I)) (by simpa using h0)
    (by intro x y; simpa [add_mul] using ha ((x : ℂ) * Complex.I) ((y : ℂ) * Complex.I))
  refine ⟨a, b, fun z => ?_⟩
  rw [← Complex.re_add_im z, ha, ha', hb', Circle.exp_add]
  simp

/-- A continuous nonzero complex-valued character of the circle is an integer power. -/
theorem exists_zpow_of_continuous_circle_mul
    (f : Circle → ℂ) (hc : Continuous f) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f x * f y) (hne : ∀ x, f x ≠ 0) :
    ∃ n : ℤ, ∀ z : Circle, f z = (z : ℂ) ^ n := by
  obtain ⟨c, hc'⟩ := exists_exp_mul_of_continuous_add
    (fun x : ℝ => f (Circle.exp x)) (hc.comp Circle.exp.continuous)
    (by simpa using h1)
    (by intro x y; rw [Circle.exp_add, hm]) (fun x => hne _)
  have hp : Complex.exp (c * (2 * Real.pi : ℝ)) = 1 := by
    rw [← hc', Circle.exp_two_pi, h1]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hp
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
  have hcn : c = (n : ℂ) * Complex.I := by
    apply mul_right_cancel₀ hpi
    calc
      c * (2 * (Real.pi : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        simpa using hn
      _ = ((n : ℂ) * Complex.I) * (2 * (Real.pi : ℂ)) := by ring
  refine ⟨n, fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Circle.exp_surjective z
  rw [hc', hcn, Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  ring

/-- A chosen coefficient for a continuous nonzero exponential on the real line. -/
def complexExponentialParameter
    (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) (hne : ∀ x, f x ≠ 0) : ℂ :=
  Classical.choose (exists_exp_mul_of_continuous_add f hc h0 ha hne)

theorem complexExponentialParameter_spec
    (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) (hne : ∀ x, f x ≠ 0) (x : ℝ) :
    f x = Complex.exp (complexExponentialParameter f hc h0 ha hne * x) :=
  Classical.choose_spec (exists_exp_mul_of_continuous_add f hc h0 ha hne) x

/-- A chosen real frequency for a continuous character of the real additive group. -/
def circleExponentialParameter
    (f : ℝ → Circle) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) : ℝ :=
  Classical.choose (exists_circle_exp_mul_of_continuous_add f hc h0 ha)

theorem circleExponentialParameter_spec
    (f : ℝ → Circle) (hc : Continuous f) (h0 : f 0 = 1)
    (ha : ∀ x y, f (x + y) = f x * f y) (x : ℝ) :
    f x = Circle.exp (circleExponentialParameter f hc h0 ha * x) :=
  Classical.choose_spec (exists_circle_exp_mul_of_continuous_add f hc h0 ha) x

/-- A chosen integer weight of a continuous nonzero complex-valued circle character. -/
def circleCharacterWeight
    (f : Circle → ℂ) (hc : Continuous f) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f x * f y) (hne : ∀ x, f x ≠ 0) : ℤ :=
  Classical.choose (exists_zpow_of_continuous_circle_mul f hc h1 hm hne)

theorem circleCharacterWeight_spec
    (f : Circle → ℂ) (hc : Continuous f) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f x * f y) (hne : ∀ x, f x ≠ 0) (z : Circle) :
    f z = (z : ℂ) ^ circleCharacterWeight f hc h1 hm hne :=
  Classical.choose_spec (exists_zpow_of_continuous_circle_mul f hc h1 hm hne) z

end Langlands.HarmonicAnalysis
