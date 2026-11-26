# The joint pointwise majorant for the ordinary real gap kernel

This module is the real counterpart of the Library's `ComplexGapOrdinaryMajorant`. Real matrices carry
the operator norm; `δ(g) = |det g|` and `H` is the real matrix height.

* `leadingInput e A Y` stacks `A` and `Y` and reindexes along `e : k + d = n`, and `exists_leading_bound`
  restates `realGapLeadingSchwartz` for it: `‖Φ(g · leadingInput A Y)‖ ≤ C H(g)^{p+q} matrixDecay p A ·
  matrixDecay q Y`.
* `normalizedDet_eq_exp`: `δ(g) = exp(∑_i alpha g i)`, from the real Iwasawa decomposition.
* `ordinaryGapNorm h Φ Ξ Ψ W V u s b g z w X Y v` is, with `B = rightTail w X v` in the block sizes `t + 1`
  and `r − t`,
  `‖Φ(B · leadingInput z Y)‖ · ‖Ξ(tailColumns B) Ψ(row_{last}(B^{-1}))‖ · ‖W(diag(g, 1) B^{-1})‖ · ‖V(g z)‖ ·
  δ(g)^u δ(z)^s δ(w)^b`.

`RealGapOrdinaryMajorantStatement` (proved by `realGapOrdinaryMajorant`): let `t < r` and let
`W : GL_{r+1}(ℝ) → ℂ`, `V : GL_{t+1}(ℝ) → ℂ` satisfy the simple-root gauge bound
`RealWhittakerTranslatedMellin.HasGaugeBound` (every vector of `realUniformWhittakerModel` does, by
`hasGaugeBound_of_mem_model`). For `A ≥ 0` there are `σ`, `τ` and `M` such that for all `u ≥ σ`, `s ≥ τ`, all
`b`, Schwartz tests `Φ`, `Ξ`, `Ψ`, orders `p`, `q`, `l` and every Haar measure `μ` on `GL_{t+1}(ℝ)`, there are
`C ≥ 0` and `j` such that `weightedMatrixTail M j s` is `μ`-integrable and

`ordinaryGapNorm … ≤ C exp(−(A + 1) ∑|alpha g i|) · weightedMatrixTail M j s z · (δ(w)^{r−t} matrixDecay p w) ·
matrixDecay q X · matrixDecay l Y`.

The proof bounds `W` at `diag(g, 1) B^{-1}` by the gauge bound, whose logarithmic coordinate is
`blockLog (alpha g) (alpha w^{-1})` by `realTwoBlockIwasawa`, and `V(g z)` by
`RealWhittakerTranslateBound.realWhittakerTranslateBound`, which costs a power of `H(z)`. The leading
test is bounded by `exists_leading_bound`, whose cost `H(B)^{j+l}` is controlled through
`H(B) δ(w)² ≤ C (1 + ‖tailColumns B‖)^{2(r+2)}` (`Langlands.GodementJacquet.realMatrixHeight_mul_absDet_sq_bound`
and `|det B| = |det w|`); the residual power `δ(w)^β` is bounded by an exponential in `∑|alpha w^{-1}|`.
Finally `realGapOrdinaryTailBound` gives the decay in the tail matrix and the rectangle, and
`exists_integrable_weightedMatrixTail` the integrability of the square factor.

The complex statement takes `W`, `V` in the complex Whittaker models and uses the explicit complex Haar
measure; the real statement uses the gauge bound only and any Haar measure. The constants reflect
`|x|` in place of `|z|_ℂ = |z|²`: `σ = A + N + N' + 1` instead of `(…)/2`, `τ = (t + 1) + 2M` instead of
`(t + 1) + M`.

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
