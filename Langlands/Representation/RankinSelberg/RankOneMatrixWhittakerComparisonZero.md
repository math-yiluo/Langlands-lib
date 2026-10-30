# Rank-one `I₁ = I₃` at actual rank one (`n = 0`)

This module proves the `n = 0` branch of the published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. At this rank
`σ` is a representation of `GL₁ = GL(0 + 1)`. The comparison is the GL₁
equal-rank (Tate) case that Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.2, printed pages 420–421
(registered as `jpss-1983-rankin-selberg`), treat directly. The module also proves
two lemmas that the positive-rank branch uses as well. It does not prove the
`n > 0` branch, and it does not assemble the full statement.

## Shared lemmas (any rank)

- `exists_eq_smul_of_linearEquiv_complex`: if `e : M ≃ₗ[ℂ] ℂ` and `m₀ ≠ 0`, then
  every `m` equals `c • m₀` for some `c : ℂ`. The proof takes
  `c = e m / e m₀`.
- `whittakerSet_eq_of_isOfWhittakerType`: if
  `IsOfWhittakerType n (standardCharacter ψ n) σ` and `ℓ.val ≠ 0`, then
  `whittakerSet ψ n σ = (coefficientModel σ ℓ).toSubmodule`. The third component
  of `IsOfWhittakerType` is a linear equivalence of all standard functionals with
  `ℂ`. So every functional is a multiple of `ℓ`, and the published
  `whittakerSet_eq_coefficientModel` gives the equality.
- `glInverseFunctionals_rankOne`: at rank one every linear form on the carrier
  of a `GL(0 + 1)` representation is an inverse-character functional
  (`glInverseFunctionals ψ 0 π = ⊤`). The group `upperUnipotent (0 + 1)` is
  trivial, so the equivariance condition is only about `u = 1`.
- `mem_inverseWhittakerSet_rankOneCharacter_one_iff`: an inverse Whittaker
  function `W'` of `GL₁` lies in the inverse Whittaker set of
  `rankOneCharacter 1` exactly when it is constant. Forward: `W'(g) = ℓ'(1 · v)
  = ℓ'(v)` for every `g`. Backward: the constant `c` is the coefficient of the
  vector `c` under the identity functional, which is allowed by the previous
  lemma.

## Test functions and constants

- `schwartzBruhatComap e Φ` pulls a Schwartz–Bruhat function back along a
  homeomorphism `e`, using the existing `Hecke.TestFunction.pullback` linear
  equivalence. Its underlying function is unchanged;
  `schwartzBruhatComap_apply` evaluates it.
- `oneByOneRow F` is the homeomorphism from `1 × 1` matrices over `F` to row
  vectors `Fin (0 + 1) → F` that takes a matrix to its last (and only) row. Its
  inverse repeats the row. `lastRow_eq_oneByOneRow` records that the published
  `lastRow g` of `g : GL(0 + 1)` is `oneByOneRow F g.val` by definition.
- `constInverseWhittaker ψ c` is the constant inverse Whittaker function of
  `GL₁` with value `c`; `constInverseWhittaker_apply` evaluates it.

## Rank-one integrals

These lemmas carry the measurable-space and Borel instances of the statement
telescope as section variables.

- `eq_rankOneQuotientHaar_of_isCompatible`: every measure `μ` on
  `LeftUnipotentQuotient 0 F` compatible with `generalLinearHaar F 0` and
  `unipotentHaar F 0` equals `rankOneQuotientHaar F`. The proof chains the
  published uniqueness `unipotentQuotientHaar_unique` with
  `unipotentQuotientHaar_zero`.
- `equalRankIntegral_rankOneQuotientHaar`: for this measure the published
  `equalRankIntegral` equals the integral of `equalRankFunction` over `GL₁`
  against `generalLinearHaar F 0` (by `integral_rankOneQuotientHaar`).
- `equalRankConverges_rankOneQuotientHaar_iff`: `EqualRankConverges` for this
  measure is integrability of `equalRankFunction` against
  `generalLinearHaar F 0`. The measure is the image of Haar measure under the
  measurable equivalence `rankOneQuotientHomeomorph.symm`, so
  `integrable_map_equiv` applies.

## Equality of value sets

`characterZetaValues_one_zero_eq` holds over any nonarchimedean local field
`F` with the instances above. It shows that, for `σ` of Whittaker type on `GL₁`,
`ℓ.val ≠ 0` and any compatible `μ`,

```text
characterZetaValues q ψ abv μ 1 0 σ
  = GodementJacquet.whittakerRationalValues q ψ abv (generalLinearHaar F 0) σ ℓ.
```

This equality of sets of rational functions is stronger than the needed equality
of spans. The proof runs as follows.

1. Replace `μ` by `rankOneQuotientHaar F` (previous section). Use
   `jpssShift 0 = 0`, so the shift `s + jpssShift 0` is `s`.
2. (⊆) Take a value given by `W ∈ whittakerSet ψ 0 σ`,
   `W' ∈ inverseWhittakerSet ψ 0 (rankOneCharacter 1)` and a vector test function
   `Φ`. By the shared lemmas, `W` lies in the coefficient model of `ℓ` and
   `W'` is a constant `c`. Take the matrix test function
   `Φ ∘ oneByOneRow` and the model vector `c • W`. The Godement–Jacquet matrix
   integrand of `c • W` is pointwise the equal-rank integrand of `(W, W', Φ)`,
   because the last row of `g` is the single entry of `g` and `W'(g) = c`. So
   convergence on the same half-plane and the same rational continuation carry
   over through the two integral lemmas above.
3. (⊇) Take a value given by a matrix test function `Φ'` and a model vector
   `w`. Use `W = w.val`, which lies in `whittakerSet` by
   `coefficientModel_subset_whittakerSet`, together with the constant inverse
   Whittaker function `1` and the vector test function `Φ' ∘ oneByOneRow⁻¹`.
   The integrands again agree pointwise, and the same two lemmas transfer
   convergence and continuation.

## The `n = 0` branch of the target

`rankOneMatrixWhittakerComparison_zero` takes the arguments of the target body at
`n = 0`: `p`, `F : PadicField p`, `ψ`, `V`, `σ`, then the Whittaker-type premise,
`ℓ`, `ℓ.val ≠ 0`, the right-invariance instance, `μ` and its compatibility. It
concludes the target's equality of Laurent submodules. The statement repeats the
target's `letI` telescope. In the proof these local instances are installed again
by `let`/`have`, and the result is `congrArg zetaSpan` applied to
`characterZetaValues_one_zero_eq`. The published wrapper
`GodementJacquet.Padic.jpssI3 F ψ σ ℓ` is by definition the span of
`whittakerRationalValues` with the residue cardinality, the normalized absolute
value and `generalLinearHaar`.
