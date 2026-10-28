# Transfer layer for the strict rank-one extension span comparison

This module holds the bookkeeping for the published target
`RankOneExtensionSpanComparisonStatement`, which formalizes Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983), Lemma (5.5),
printed pages 423–427 (registered as `jpss-1983-rankin-selberg`). The source's
argument relates the block-one integrals of `π × σ₁` to block-zero integrals of `π`
against the induced representation. This module proves the formal step from
pointwise identities `Ψ_ind(s) = c · Ψ_base(s)`, with `c ≠ 0` on a right half-plane,
to the inclusion of Laurent spans. It also proves the matrix and integrand
identities that relate the two zeta integrals at a common rank. It contains no
analytic comparison: no compact section, Jacquet functional, unfolding, Fourier
cutoff or convergence estimate is constructed or proved here. The names, the rank
cast and the shape of the pointwise premise are internal implementation choices.

## Rank cast

The published `unequalRankZetaValuesAt j k hr …` takes the large representation `π`
at rank `r` together with a proof `hr : r = n + (j + k + 1)`, and is defined by
substituting `hr`. To state the pointwise premise without substituting, the module
uses `rankCastWhittaker ψ h W`, an abbreviation of the existing
`InducedTailIntermediate.whittakerRankCast` in the shared
[WhittakerRankCast](WhittakerRankCast.md) module. Its equality-substitution body
transports a Whittaker function along `h : m = m'`. This shared import avoids a
dependency on the intermediate-tail comparison. The lemma
`rankCastWhittaker_apply` evaluates the transported function
at `g` as `W` at the entry-preserving reindex `(reindex (finCongr _)).symm g`. So the
cast changes no matrix entry. `rankCastWhittaker_rfl` is the trivial case.

`mem_unequalRankZetaValuesAt_iff` unpacks membership in `unequalRankZetaValuesAt`
with `W₀` kept in `whittakerSet ψ r π` at the large rank. It reads: there are `W₀`
and `W' ∈ inverseWhittakerSet ψ n σ` such that the integral of
`rankCastWhittaker ψ hr W₀` against `W'` converges absolutely on some right
half-plane and continues to the given rational function.

## Span glue and the general transfer

- `zetaSpan_le_of_forall_exists_const_mul`: if every element of `S` has a nonzero
  constant multiple `C c * R` in `T`, then `zetaSpan S ≤ zetaSpan T`. The proof
  multiplies by the Laurent constant `c⁻¹`.
- `hasRationalContinuation_of_eq_const_mul`: if `g s = c * f s` on a right
  half-plane and `f` continues to `R`, then `g` continues to `C c * R`. This uses the
  published `hasRationalContinuation_const_mul`.
- `zetaSpan_unequalRankZetaValuesAt_le_of_pointwise` is the general transfer between
  two block data `(n, j, k, μ, ν, σ)` and `(n', j', k', μ', ν', σ')` for the same `π`
  at rank `r`. The second representation may live in an independent universe. Its
  premise `H` is as follows. Take any `W₀ ∈ whittakerSet ψ r π` and
  `W' ∈ inverseWhittakerSet ψ n σ` whose first integral converges absolutely on a
  right half-plane. Then there are `W₁ ∈ whittakerSet ψ r π`,
  `W'' ∈ inverseWhittakerSet ψ n' σ'`, a constant `c ≠ 0` and a bound `a'` such
  that, for `a' < Re s`, the second integral of `W₁, W''` converges absolutely and
  equals `c` times the first integral of `W₀, W'`. The conclusion is the inclusion
  of the Laurent span of the first zeta values in that of the second. The proof
  unpacks a first zeta value and applies `H`. The convergence part of `H` gives the
  convergence clause of the second value. The identity, with the two glue lemmas,
  gives the continuation `C c * R` and the inclusion.

## The statement-shaped instance

`rankOneExtensionSpanComparison_of_pointwise` states the general transfer with the
exact data of `RankOneExtensionSpanComparisonStatement`:

- the same `p`, `F`, `ψ`, `ν`, `π`, `σ₁`, `χ` and lifted character `χlift`;
- the same topology, valuation, local-field and Borel instances;
- block one with predecessor rank `t` and `rectangularMeasure ν.val 1 (t + 1)`;
- block zero with predecessor rank `1 + t`, `rectangularMeasure ν.val 0 ((1 + t) + 1)`
  and `rankOneExtensionLowerInduced F t χlift σ₁`.

The trailing index `k` and both rank equations `hrB`, `hrI` are arbitrary
hypotheses. The statement is the case `k = r - t - 2` with its own proofs `hrBase`
and `hrInd`. The Haar-invariance and compatibility premises of the statement are not
needed for this step and do not appear. The remaining premise is exactly `H` above
for these data.

## Matrices

All matrix lemmas hold over an arbitrary field.

- `rankInclusion_entry` gives the entries of `rankInclusion d g = diag(g, I_d)`.
- `rankOneExtensionLowerBlock_entry`, imported from
  [RankOneExtensionCellAlgebra](RankOneExtensionCellAlgebra.md), gives the entries of the published lower block
  `[m, 0; x, a]` in `GL(1 + (t + 1))` by numeric index. The large block comes first
  and the scalar row has index `t + 1`.
- `rankOneExtensionLowerBlock_eq_mul` and
  `rankOneExtensionEmbeddedLowerBlock_eq_mul` give the factorization
  `[m, 0; x, a] = [m, 0; x, 1] · [I, 0; 0, a]`, before and after `rankInclusion`.
- `reindex_symm_unequalRankMatrix_one`: the published block-one matrix
  `unequalRankMatrix 1 k g x = [g, 0, 0; x, 1, 0; 0, 0, I_(k+1)]`, reindexed from
  rank `t + (1 + k + 1)` to rank `(1 + (t + 1)) + k`, is the embedded lower block
  `rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1`.
- `reindex_symm_appendIdentity_reindex`: for `g ∈ GL(1 + (t + 1))`, the block-zero
  matrix `appendIdentity (1 + t) (0 + k + 1)` of the cast of `g` to
  `GL((1 + t) + 1)`, reindexed to rank `(1 + (t + 1)) + k`, is
  `rankInclusion (k + 1) g`.
- `determinantWeight_reindex_finCongr`: the determinant weight is unchanged by the
  entry-preserving reindex.

## Integrands

These lemmas use the casts at the large rank `(1 + (t + 1)) + k`, which is `r` when
`k = r - t - 2`.

- `rankCastWhittaker_unequalRankMatrix_one`: the cast function on the block-one
  matrix equals `W` on `rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1`.
- `rankCastWhittaker_appendIdentity_reindex` and
  `rankCastWhittaker_appendIdentity_lowerBlock`: the cast function on the
  block-zero matrix of a cast element `g` (respectively of the lower block
  `[m, 0; x, a]`) equals `W` on `rankInclusion (k + 1) g` (respectively on the
  embedded lower block with the same `m, x, a`).
- `unequalRankIntegrand_rankCast_one_mk`: the block-one integrand at the class of
  `g` is
  `W(embedded lower block of g, x 0, 1) · W'(g) · determinantWeight abv g (s - (1 + k + 1)/2)`.
- `unequalRankIntegrand_rankCast_zero_mk`: the block-zero integrand at the class of
  the cast of `g ∈ GL(1 + (t + 1))` is
  `W(rankInclusion (k + 1) g) · W''(cast g) · determinantWeight abv g (s - (0 + k + 1)/2)`.

Together these lemmas rewrite both integrands of Lemma (5.5) into the coordinates of
`RankOneExtensionAnalyticData`. Any comparison of the integrals themselves is left
to later modules.
