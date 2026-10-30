# Rank-one character zeta values at actual rank at least two

This module rewrites the left side of the positive-rank branch (`n = m + 1`) of
the published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. At this rank
`σ` acts on `GL(m + 1 + 1)`. The left side is the Library's rank-one character
zeta value set `characterZetaValues q ψ abv μ 1 (m + 1) σ`. This is the integral
`Ψ(s, W)` of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), Section 5.2, equation (1), printed page 420 (registered as
`jpss-1983-rankin-selberg`), with the trivial character of `GL₁`.

The module identifies this set with the reduced set `rankOneModelValues` of the
definitions-only module `RankOneMatrixWhittakerComparisonValues`, integrated
against `generalLinearHaar F 0`. It does not compare that set with the
Godement–Jacquet side, and it does not assemble the full statement.

## How the Library packages the left side

For `m + 1 > 0` the published definition `characterZetaValues` is the block
family of unequal-rank values with `j = 0` rectangular rows and gap `k = m`. Three
pieces of packaging are removed here:

- The representation is `σ.comp (characterPairRank m)`, where
  `characterPairRank m` is the identity relabelling from rank
  `0 + (0 + m + 1) + 1` to rank `m + 1 + 1`.
- The rectangular variable lies in the zero-row matrix space
  `Matrix (Fin 0) (Fin (0 + 1)) F`, which carries the unit point mass at `0`
  and the discrete measurable structure.
- The inverse Whittaker functions of `GL₁` range over the set of the trivial
  character `rankOneCharacter 1`. The `n = 0` module shows that these are exactly
  the constant functions.

## Point masses

- `measure_prod_dirac_eq_map`: for any measure `μ`, the product
  `μ.prod (dirac b)` equals the image of `μ` under `x ↦ (x, b)`. The proof
  evaluates both sides on a measurable set with `Measure.prod_apply`. No
  σ-finiteness is assumed. This matters because instance search finds no
  `SFinite` instance for `generalLinearHaar F 0` or `rankOneQuotientHaar F`, so
  Mathlib's `Measure.prod_dirac` does not apply.
- `prodUniqueMeasurableEquiv`: if `β` has exactly one point, then `α × β` is
  measurably equivalent to `α`.
- `integrable_prod_dirac_iff`: if `β` has one point, then a function on `α × β`
  is integrable for `μ.prod (dirac b)` exactly when `x ↦ f (x, b)` is
  integrable for `μ`. This combines the two facts above with
  `integrable_map_equiv`.

## Relabelling and the embedding

- `whittakerSet_comp_reindex`: if `h : N = M`, the all-functional Whittaker set
  of `σ ∘ reindex (finCongr (congrArg (· + 1) h))` is the image of
  `whittakerSet ψ M σ` under the published rank cast
  `InducedTailIntermediate.whittakerRankCast ψ h.symm`. After `subst h` the
  relabelling is the identity (`reindex_finCongr_rfl`) and the rank cast is the
  identity by definition. `characterPairRank m` is by definition such a
  relabelling.
- `characterPairRank_appendIdentity_val`: the published block inclusion
  `appendIdentity 0 (0 + m + 1)`, which is what `unequalRankMatrix 0 m g x`
  reduces to when there are no rows (`unequalRankMatrix_zero_rows`), read through
  `characterPairRank m`, is the diagonal matrix with entries `g₀₀, 1, …, 1`. The
  proof is entrywise from `appendIdentity_entry`.
- `rankOneEmbedding_val`: the embedding
  `rankOneEmbedding m g = diag(det g, 1, …, 1)` of the Values module is the same
  diagonal matrix, because the determinant of a `1 × 1` matrix is its entry
  (`Matrix.det_fin_one`).
- `characterPairRank_appendIdentity`: hence the two elements of `GL(m + 1 + 1)`
  are equal.

## Integrands

- `rankOneModelIntegrand_smul`: replacing the model vector `w` by `c • w`
  multiplies the integrand `rankOneModelIntegrand ψ abv σ ℓ w s` by `c`.
- `unequalRankIntegrand_whittakerRankCast`: let `W` be a Whittaker function of
  rank `m + 1` and let `W'` be the constant inverse Whittaker function `c`. Then
  the published unequal-rank integrand of the rank cast of `W` and of `W'`, at
  any rectangular point `x` and at the class of `g`, equals
  `c · W(diag(det g, 1, …, 1)) · |det g|^(s - (m+1)/2)`. The published exponent is
  `s - (0 + m + 1)/2`, which is the same number.

## Equality of value sets

`characterZetaValues_one_succ_eq` holds over any nonarchimedean local field `F`.
It carries the measurable-space and Borel instances of the statement telescope as
section variables. It assumes that `σ` is of Whittaker type at rank `m + 1`, that
`ℓ.val ≠ 0`, and that `μ` is compatible with `generalLinearHaar F 0` and
`unipotentHaar F 0`. Under these assumptions,

```text
characterZetaValues q ψ abv μ 1 (m + 1) σ
  = rankOneModelValues q ψ abv (generalLinearHaar F 0) σ ℓ.
```

The proof runs as follows.

1. Replace `μ` by `rankOneQuotientHaar F` (`eq_rankOneQuotientHaar_of_isCompatible`
   from the `n = 0` module). Give the zero-row matrix space the discrete
   measurable structure that the definition uses, and its unique element.
2. For a rank-cast Whittaker function and a constant inverse Whittaker function
   `c`, rewrite convergence. `integrable_prod_dirac_iff` removes the point mass.
   `integrable_map_equiv` along `rankOneQuotientHomeomorph.symm` passes from the
   quotient to `GL₁`, since `rankOneQuotientHaar F` is the image of
   `generalLinearHaar F 0`. The integrand lemma above then gives integrability
   of `c` times the rank-one integrand. The integral is rewritten the same way,
   using `integral_dirac` and `integral_rankOneQuotientHaar`.
3. The Whittaker set of the relabelled representation is the rank-cast image of
   the coefficient model of `ℓ` (`whittakerSet_comp_reindex` and
   `whittakerSet_eq_of_isOfWhittakerType` from the `n = 0` module).
4. (⊆) A value comes from `W` in the coefficient model and a constant `W' = c`
   (`mem_inverseWhittakerSet_rankOneCharacter_one_iff`). The model vector
   `c • W` has integrand `c` times that of `W`. So it converges on the same
   half-plane and has the same rational continuation.
5. (⊇) A value comes from a model vector `w`. Use `W = w.val` together with
   the constant inverse Whittaker function `1` (`constInverseWhittaker ψ 1`).
   With `c = 1` the two integrands agree.

The two value sets are equal as sets, not only after taking spans.
