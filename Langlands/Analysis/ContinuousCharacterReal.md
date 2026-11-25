# Continuous complex characters of the real line

`Langlands.ContinuousCharacterReal.exists_eq_exp` proves that a continuous
`φ : ℝ → ℂ` with `φ 0 = 1` and `φ (u + v) = φ u * φ v` satisfies
`φ u = Complex.exp (c * u)` for some `c : ℂ`.

The proof picks a short interval on which `φ` stays within distance one half
of 1. Its integral `A` on that interval is nonzero. Translating the interval
multiplies the integral by `φ u`, so the fundamental theorem of calculus
gives `φ' = c φ`, with `c = (φ e − 1)/A` for interval length `e`. The
derivative of `φ u exp(−c u)` vanishes and its value at zero is 1.

This is an internal proof of the character fact needed for the norm-power
normalization used in the proof of Jacquet–Shalika II, Theorem 4.2, display
(1), printed p. 806 (PDF p. 31).
