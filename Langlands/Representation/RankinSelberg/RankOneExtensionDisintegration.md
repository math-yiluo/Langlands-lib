# Lower-block disintegration at the rank of the rank-one extension

This module adapts the published lower-block chart and the published
proposition `LowerBlockQuotientDisintegrationStatement` to the ranks used in
the strict rank-one extension comparison
`RankOneExtensionSpanComparisonStatement` (JPSS Lemma (5.5)). It has a base
quotient `N_(t+1) \ GL_(t+1)` and a full quotient
`N_((1+t)+1) \ GL_((1+t)+1)`. The module proves no new disintegration
formula. The disintegration proposition is an explicit hypothesis of the
specialization theorem.

## Contents

`rankOneExtensionQuotientChart` is the map

```text
([g], x, h) ↦ [[g, 0], [x, h]]
```

from `LeftUnipotentQuotient t K × (M_(1×(t+1))(K) × B⁻_1(K))` to
`LeftUnipotentQuotient (1 + t) K`. Here `B⁻_1` is the `1 × 1` lower-triangular
group `lowerTriangularSubgroup 1 K`. The map is defined as the published
`lowerBlockQuotientChart` with `a = t + 1` and `d = 1`, which lands in rank
`t + 1 + 1`. It is followed by the published coset relabelling
`upperUnipotentQuotientCongr` for the rank equality `t + 1 + 1 = (1 + t) + 1`.
No other modification is made.

`rankOneExtensionQuotientChart_mk` evaluates the chart at a representative
`g ∈ GL_(t+1)(K)`. For every proof `hc : 1 + (t + 1) = (1 + t) + 1`, the image of
`([g], x, h)` is the coset of `reindex (finCongr hc) B`. Here `B` is the
published unit
`rankOneExtensionLowerBlock t g (x 0) a = [g, 0; x 0, a]` of `GL_(1+(t+1))(K)`,
and `a` is the nonzero entry `lowerScalarEntry h` of `h` as a unit. The proof
compares entries. Both sides are the block matrix `fromBlocks g 0 x h`, read
through `finSumFinEquiv` on one side and through
`rankOneExtensionCellCoordinates t = finSumFinEquiv.trans (finCongr _)` on the
other. The two index maps agree after the casts, which is checked on natural
number values. The four block cases then close by `rfl`, using that
`Fin 1` is a subsingleton.

`rankOneExtensionDisintegration_of_statement` takes as hypothesis
`hdis : LowerBlockQuotientDisintegrationStatement` and specializes it at
`n = t` and `k = 0` for a `p`-adic field `F`. All topologies and Borel
structures are the canonical ones of `F`. It takes an additive Haar measure
`η` on `F` and right invariance of the unipotent Haar measures in ranks
`t + 1` and `(1 + t) + 1`. It also takes a quotient measure `μbase` compatible
with the normalized Haar measures in rank `t + 1`, and a quotient measure
`μind` compatible with them in rank `(1 + t) + 1`. From these it produces a
measure `ρ` on `B⁻_1(F)` and a real scalar `C > 0`. The measure `ρ` is
regular, sigma-finite, positive on open sets, finite on compact sets and
right invariant. For every Borel measurable `f : N_((1+t)+1) \ GL_((1+t)+1) → ℂ`:

- `f` is `μind`-integrable exactly when `f ∘ rankOneExtensionQuotientChart` is
  integrable for
  `P = (μbase.withDensity D) ⊗ (rectangularMeasure η 1 (t+1) ⊗ ρ)`;
- for `μind`-integrable `f`,
  `∫ f dμind = C · ∫ f(rankOneExtensionQuotientChart z) dP(z)`.

Here `D = lowerBlockQuotientDensity F.canonicalTopologicalData (t+1) 1` is the
published determinant density `|det g|^(-1)` on the base quotient. The scalar,
the measure `ρ` and both supplied compatible measures are kept as in the
statement.

## Proof

The proof follows the published
`InducedTailIntermediate.disintegration_transfer_of_statement` with `n = t`
and `k = 0`. The statement is stated for the full rank `t + 1 + 0 + 1`. The proof
moves `μind` to that rank with the public `quotientMeasureRankCast` along
`t + 1 + 0 = 1 + t`, and uses `compatible_quotientMeasureRankCast_iff` to keep
compatibility. Right invariance of the unipotent Haar measure is moved along
the same equality. Then it applies `hdis` to `μbase` and the moved measure. The
function `f` is pulled back along `upperUnipotentQuotientCongr`. Measurability,
integrability and integrals transfer back through
`measurable_comp_upperUnipotentQuotientCongr`,
`integrable_quotientMeasureRankCast_iff` and `integral_quotientMeasureRankCast`.
The pulled-back function composed with the published chart is definitionally
`f ∘ rankOneExtensionQuotientChart`. The density and rectangular measure at
`k = 0` are definitionally those in the conclusion. The two private helper
lemmas, `quotientMeasureRankCast_symm` (casting there and back is the
identity) and `unipotentHaar_rightInvariant_of_index_eq`, are local copies of
the private lemmas of the same names in
`InducedTailIntermediateDisintegrationTransfer`. Both are proved by `subst`.

## Source and provenance

This is internal infrastructure, derived by rank transport from published
Library declarations. The underlying calculation is the lower-block
disintegration of H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
section 9.3, printed page 456. The source is registered as
`jpss-1983-rankin-selberg`. Its formalized form is the published proposition
`LowerBlockQuotientDisintegrationStatement`, whose Markdown records the exact
source passage. That passage uses lower-block rank `d = t − r₂`. Here it is
used with lower-block rank `1`, the case `t₂ = 1` of the proof of Lemma (5.5).
In that proof, printed page 424 writes `Ψ(s, W, W_f; 0)` as an integral over
the quotient `N_{t₁,t₂} \ G_t` (display (4)). Printed page 425 writes elements of
the lower parabolic `Q` as `[1, 0; y, 1][m, 0; 0, a]` with `m ∈ G_{t₁}` and
`a ∈ F^×`, which is the lower-block form `[m, 0; x, a]` of this chart. Both
pages were rendered and read (one-based PDF pages 59–60). The chart rank and its expression through
`rankOneExtensionLowerBlock` were requested by Worker 802 for the assembly of
the strict span comparison. They make the chart match the integrand
coordinates of `RankOneExtensionSpanTransfer`.
