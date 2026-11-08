# The dual integrand on the lower-block chart

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, formulas (5)–(9), printed page 328).

- `determinant_inverseTranspose`: `det(ᵗg⁻¹) = (det g)⁻¹`.
- `determinant_lowerBlockPair`: `det [[A,0],[x,c]] = det A · det c`, from the published
  determinant of the lower-block localization.
- `lowerBlockPair_eq_mul_diag`: `[[A,0],[x,c]] = [[A,0],[x,1]] · diag(I, c)`.
- `det_gl_one_val`: the determinant of a `1 × 1` matrix is its entry.
- `whittaker_dualConj_eq_zero_of_not_integral`: if the reversed last row `ξ(h)` has a
  non-integral coordinate `ξ_k`, a Whittaker function right invariant under the level
  subgroup vanishes at `M(h)`. Indeed `n(z)` with `z = z₀ e_k`, `z₀` integral, lies in the
  level subgroup, and `W(M(h) n(z)) = ψ(z₀ ξ_k) W(M(h))` with `ψ(z₀ ξ_k) ≠ 1`. Hence the
  factorization of the exponential sum is needed only at integral `ξ`.
- `candidateTest_dual_lowerBlockPair`: the dual corank-one integrand of the candidate test
  function, at `h = [[A,0],[x,c]]`, separates as
  `χ(det w) · [S1(c) χ(c)⁻¹ η(c)] · [S2(rev x) χ(det A)⁻¹ f̃([[A,0],[x,1]]) |det A|^(s-1/2) W(M(diag(A,1)))]`.
  The hypotheses are: the exponential sum factors as `S1(ξ_0) S2(ξ_rest)` at integral `ξ`; `S1` is
  supported on integral units and `S2` on `𝔭^f`; `W` is right invariant under the level-`f`
  subgroup; the dual test `f̃` satisfies `f̃(y · diag(I,c)) = η(c) f̃(y)` for integral units
  `c`; `abv` is trivial on integral units; and `ψ` is nontrivial on `z t` for some integral
  `z` whenever `t` is not integral. Off the support both sides vanish; on it,
  `whittaker_dualConj_lowerBlockPair` removes `x` and `c` from the Whittaker factor, the
  determinant of `w ᵗdiag(h,1)⁻¹` is `det w · (det A det c)⁻¹`, and `|det h| = |det A|`.
  This replaces the source's choices (6)–(8) by explicit hypotheses on the weights.
