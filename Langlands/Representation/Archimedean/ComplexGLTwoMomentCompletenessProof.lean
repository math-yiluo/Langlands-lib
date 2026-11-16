import Langlands.Representation.Archimedean.ComplexGLTwoLadder
import Langlands.Representation.Archimedean.ComplexGLTwoWeylBound
import Langlands.Representation.Archimedean.ComplexGLTwoRadial

/-!
# Nonvanishing of low moments on submodules of the `GL_2(ℂ)` principal series

Proof of `ComplexGLTwoMomentCompletenessStatement`. Let `s = t_0 - t_1` with `Re s > 0`,
`m = l_0 - l_1`, `p = s + m / 2`, `q = s - m / 2`, and let `S ≠ 0` be a `(𝔤, K)`-submodule
of `X(d)`.

* `S` contains a vector with noncompact picture `φ_b(z) = (1 + |z|²)^(-(q + 1 + b)) z̄^b`
  (`exists_phiB_mem`), and every such `b` satisfies `m ≤ b` (`weight_sub_le`).
* Lowering `b` with the ladder identity (`exists_phiB_pred_mem`) as long as possible gives
  such a vector with `b = 0`, `b = m` or `b = p` (`exists_phiB_mem_stop`).
* If `m ≤ 0`, then `M_{b,0} f_b = ∫ (1 + |z|²)^(-(q + 1 + b)) |z|^(2b) dz ≠ 0`, and
  `b ≤ Re s`.
* If `m > 0`, then `M_{0,b-m} (ρ(w) f_b) = ± ∫ (1 + |z|²)^(-(q + 1 + b)) |z|^(2(b - m)) dz ≠ 0`,
  and `b - m ≤ Re s`.

The radial integrals are nonzero by `radInt_ne_zero`.
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

variable {d : Fin 2 → ComplexCharacterData}

/-- Lowering a vector with noncompact picture `φ_b` in a `(𝔤, K)`-submodule until the ladder
coefficient vanishes. -/
theorem exists_phiB_mem_stop (S : Submodule ℂ (Xd d))
    (hS : IsGKSubmodule (complexStandardRep 2 (List.ofFn d)) (πd d) S) :
    ∀ (b : ℕ) (v : Xd d), v ∈ S → ncpL d v = phiB d b →
      ∃ (c : ℕ) (w : Xd d), w ∈ S ∧ ncpL d w = phiB d c ∧
        (c = 0 ∨ (c : ℤ) = (d 0).weight - (d 1).weight ∨ (c : ℂ) = pp d) := by
  intro b
  induction b with
  | zero =>
    intro v hvS hv
    exact ⟨0, v, hvS, hv, Or.inl rfl⟩
  | succ n ih =>
    intro v hvS hv
    by_cases hc : ((n : ℂ) + 1) * ((n : ℂ) + 1 - mC d) * ((n : ℂ) + 1 - pp d) *
        (lD d n + 2) = 0
    · refine ⟨n + 1, v, hvS, hv, Or.inr ?_⟩
      have hm := weight_sub_le hv
      rcases mul_eq_zero.mp hc with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exfalso
            have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
            push_cast at hn
            exact hn h
          · left
            unfold mC at h
            have h' : (((n + 1 : ℕ) : ℤ) : ℂ) = (((d 0).weight - (d 1).weight : ℤ) : ℂ) := by
              push_cast at h ⊢
              linear_combination h
            exact Int.cast_inj.mp h'
        · right
          push_cast
          linear_combination h
      · exfalso
        unfold lD mC at h
        have h' : ((2 * ((n : ℤ) + 1) - ((d 0).weight - (d 1).weight) + 2 : ℤ) : ℂ) = 0 := by
          push_cast at h ⊢
          linear_combination h
        have h'' := Int.cast_eq_zero.mp h'
        push_cast at hm
        omega
    · obtain ⟨w, hwS, hw⟩ := exists_phiB_pred_mem S hS hvS hv hc
      exact ih w hwS hw

/-- The moment `M_{i,j}` in the noncompact picture. -/
theorem moment_eq (v : Xd d) (i j : ℕ) :
    complexGLTwoMoment i j (v : Langlands.GeneralLinear 2 ℂ → ℂ) =
      ∫ z : ℂ, ncpL d v z * z ^ i * conj z ^ j := by
  unfold complexGLTwoMoment
  congr 1
  funext z
  rw [weyl_mul_unipotent]
  rfl

theorem moment_phiB {v : Xd d} {b : ℕ} (hv : ncpL d v = phiB d b) :
    complexGLTwoMoment b 0 (v : Langlands.GeneralLinear 2 ℂ → ℂ) =
      radInt (-(qq d + 1 + b)) b := by
  rw [moment_eq, hv, radInt]
  congr 1
  funext z
  rw [phiB, rad, mul_pow]
  ring

theorem moment_rho_wU {v : Xd d} {b c : ℕ} (hv : ncpL d v = phiB d b)
    (hc : (c : ℤ) = b - ((d 0).weight - (d 1).weight)) :
    complexGLTwoMoment 0 c
        ((complexStandardRep 2 (List.ofFn d) wU v : Xd d) :
          Langlands.GeneralLinear 2 ℂ → ℂ) =
      (-1) ^ (d 0).weight * radInt (-(qq d + 1 + b)) c := by
  rw [moment_eq, ncpL_rho_wU_eq hv hc, radInt, ← integral_const_mul]
  congr 1
  funext z
  rw [rad, mul_pow]
  ring

theorem qq_re : (qq d).re = (d 0).exponent.re - (d 1).exponent.re -
    (((d 0).weight - (d 1).weight : ℤ) : ℝ) / 2 := by
  have h : qq d = (d 0).exponent - (d 1).exponent -
      (((((d 0).weight - (d 1).weight : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    unfold qq
    push_cast
    ring
  rw [h, Complex.sub_re, Complex.sub_re, Complex.ofReal_re]

theorem pp_re : (pp d).re = (d 0).exponent.re - (d 1).exponent.re +
    (((d 0).weight - (d 1).weight : ℤ) : ℝ) / 2 := by
  have h : pp d = (d 0).exponent - (d 1).exponent +
      (((((d 0).weight - (d 1).weight : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    unfold pp
    push_cast
    ring
  rw [h, Complex.add_re, Complex.sub_re, Complex.ofReal_re]

theorem neg_qq_re_add (b c : ℕ) :
    (-(qq d + 1 + b)).re + c = -(qq d).re - 1 - b + c := by
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.natCast_re]
  ring

end ComplexGLTwoNoncompact

open ComplexGLTwoNoncompact in
/-- Every nonzero `(𝔤, K)`-submodule of the `U(2)`-finite principal series `X(d)` with
`Re t_1 < Re t_0` contains a function with a nonzero moment `M_{i,j}`,
`i + j ≤ Re(t_0 - t_1)`. -/
theorem complexGLTwoMomentCompleteness : ComplexGLTwoMomentCompletenessStatement := by
  intro d hd S hS hne
  obtain ⟨n, v, hvS, hv⟩ := exists_phiB_mem S hS hne
  obtain ⟨b, w, hwS, hw, hb⟩ := exists_phiB_mem_stop S hS n v hvS hv
  have hm := weight_sub_le hw
  have hqre := qq_re (d := d)
  have hpre := pp_re (d := d)
  by_cases hm0 : (d 0).weight - (d 1).weight ≤ 0
  · have hm0' : ((((d 0).weight - (d 1).weight : ℤ)) : ℝ) ≤ 0 := by exact_mod_cast hm0
    refine ⟨b, 0, w, hwS, ?_, ?_⟩
    · rw [add_zero]
      rcases hb with h | h | h
      · subst h
        simp only [Nat.cast_zero]
        linarith
      · have h0 : b = 0 := by omega
        subst h0
        simp only [Nat.cast_zero]
        linarith
      · have h' := congrArg Complex.re h
        rw [Complex.natCast_re, hpre] at h'
        linarith
    · rw [moment_phiB hw]
      apply radInt_ne_zero
      rw [neg_qq_re_add]
      linarith
  · push Not at hm0
    have hm0' : 0 < ((((d 0).weight - (d 1).weight : ℤ)) : ℝ) := by exact_mod_cast hm0
    obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ℤ) = b - ((d 0).weight - (d 1).weight) :=
      ⟨(b - ((d 0).weight - (d 1).weight)).toNat, by omega⟩
    have hcR : (c : ℝ) = b - ((((d 0).weight - (d 1).weight : ℤ)) : ℝ) := by
      exact_mod_cast hc
    refine ⟨0, c, complexStandardRep 2 (List.ofFn d) wU w, hS.1 wU w hwS, ?_, ?_⟩
    · rw [zero_add]
      rcases hb with h | h | h
      · omega
      · have h0 : c = 0 := by omega
        subst h0
        simp only [Nat.cast_zero]
        linarith
      · have h' := congrArg Complex.re h
        rw [Complex.natCast_re, hpre] at h'
        linarith
    · rw [moment_rho_wU hw hc]
      refine mul_ne_zero (zpow_ne_zero _ (by norm_num)) (radInt_ne_zero ?_)
      rw [neg_qq_re_add]
      linarith

end Langlands.Archimedean
