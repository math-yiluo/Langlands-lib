import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement
import Langlands.Representation.Archimedean.PairBlockExponent

/-!
# Right half-plane regularity of real pair `L`-factors

A proof of `Langlands.Archimedean.RealPairLFactorRightHalfPlaneRegularityStatement`: the real
pair `L`-factor `realPairLFactor ds ds'` has no pole at `s` when `Re(s) + Re(t) + Re(t') > 0`
for every block exponent `t` of `ds` and `t'` of `ds'`. Its poles lie where the shifted
argument `s + t + t' + ε` of a `Γ_ℝ` factor is a nonpositive even integer, or the shifted
argument `s + t + t' + |m|/2` of a `Γ_ℂ` factor is a nonpositive integer. See the paired
Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- **Right half-plane regularity of real pair `L`-factors.** Each block of the pair
presentation has real exponent `Re(t) + Re(t')`, and its pole condition
`s + (t + t' + ε) = -2k` or `s + (t + t' + |m|/2) = -k` with `ε, |m|/2, k ≥ 0` would force
`Re(s) + Re(t) + Re(t') ≤ 0`. -/
theorem realPairLFactorRightHalfPlaneRegularity :
    RealPairLFactorRightHalfPlaneRegularityStatement := by
  intro ds ds' s h
  rw [realPairLFactor, realLFactor_regular_iff]
  refine ⟨fun d hd k hk => ?_, fun d hd k hk => ?_⟩
  · obtain ⟨x, hx, y, hy, he⟩ := exists_realBlockExponent_of_mem_realPairBlocks hd
    have hpos := h x hx y hy
    have hre := congrArg Complex.re hk
    have he' : d.exponent.re = realBlockExponent x + realBlockExponent y := he
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, zero_mul, sub_zero] at hre
    have hp : (0 : ℝ) ≤ (d.parity.val : ℝ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  · obtain ⟨x, hx, y, hy, he⟩ := exists_realBlockExponent_of_mem_realPairBlocks hd
    have hpos := h x hx y hy
    have hre := congrArg Complex.re hk
    have he' : d.exponent.re = realBlockExponent x + realBlockExponent y := he
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.div_ofNat_re] at hre
    have hw : (0 : ℝ) ≤ (d.weight.natAbs : ℝ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith

end Langlands.Archimedean
