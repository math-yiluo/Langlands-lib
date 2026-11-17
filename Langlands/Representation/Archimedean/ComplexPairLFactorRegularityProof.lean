import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement
import Langlands.Representation.Archimedean.PairBlockExponent

/-!
# Right half-plane regularity of complex pair `L`-factors

A proof of `Langlands.Archimedean.ComplexPairLFactorRightHalfPlaneRegularityStatement`: the
complex pair `L`-factor `complexPairLFactor ds ds'` has no pole at `s` when
`Re(s) + Re(t) + Re(t') > 0` for every exponent `t` of `ds` and `t'` of `ds'`. Its poles lie
where a shifted argument `s + t + t' + |m|/2` of `Γ_ℂ` is a nonpositive integer. See the
paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- **Right half-plane regularity of complex pair `L`-factors.** Each character of the pair
presentation is a product `x.mul y` with exponent `t + t'`, and its pole condition
`s + (t + t' + |m|/2) = -k` with `|m|/2, k ≥ 0` would force `Re(s) + Re(t) + Re(t') ≤ 0`. -/
theorem complexPairLFactorRightHalfPlaneRegularity :
    ComplexPairLFactorRightHalfPlaneRegularityStatement := by
  intro ds ds' s h
  rw [complexPairLFactor, complexLFactor_regular_iff]
  intro d hd k hk
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_complexPairBlocks.mp hd
  have hpos := h x hx y hy
  have hre := congrArg Complex.re hk
  simp only [ComplexCharacterData.exponent_mul, Complex.add_re, Complex.natCast_re,
    Complex.neg_re, Complex.div_ofNat_re] at hre
  have hw : (0 : ℝ) ≤ ((x.mul y).weight.natAbs : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  linarith

end Langlands.Archimedean
