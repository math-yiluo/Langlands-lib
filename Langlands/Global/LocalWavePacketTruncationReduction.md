# Lapid's Proposition 2 from the limit of truncated inner products, for one compact subgroup

Module `Langlands.Global.LocalWavePacketTruncationReduction` states two
propositions and proves one implication between them:

- `Langlands.Global.LocalWavePacketInnerProductTruncationCompactStatement`: Lapid's
  Proposition 2 for wave packets in `W_P` (as in
  `LocalWavePacketInnerProductStatement`) under three additional hypotheses
  on the compact subgroup `K`, which make the truncation operator with
  respect to `K` available;
- `Langlands.Global.TruncatedWavePacketLimitStatement`: the sufficient
  condition with which Lapid begins the proof of Proposition 2, for the same
  data;
- `Langlands.Global.localWavePacketInnerProductTruncationCompact_of_truncatedLimit`:
  the second statement implies the first.

The module proves neither statement.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: the conventions, among them a maximal compact `K` of `G(𝔸)` "in
    good position with respect to `M₀`"; p.312: the truncation operator `Λ^T`.
  - §3, p.314: Proposition 2 and formula (4).
  - Lemma 9 and its proof, p.327: `(Λ^T F, F) = ‖Λ^T F‖² ≤ ‖F‖²`, `Λ^T F = F`
    on a growing family of Siegel regions, and monotone convergence.
  - §8, p.328, first paragraph: "By Lemma 9 it suffices to show that the inner
    product `(Λ^T Θ_{P,φ}, Λ^T Θ_{P',φ'})_{G\G(𝔸)}` converges to the
    right-hand side of (4) as `T → ∞` in `C`."
- J. Arthur, *An introduction to the trace formula* (2005), §13, Proposition
  13.1 and the paragraph after its proof, pp. 68–69, in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: `Λ^T` extends to
  an orthogonal projection on `L²(G(F) \ G(𝔸))`; Proposition 13.2, pp. 69–71:
  truncations of functions of uniform moderate growth decrease rapidly. §4,
  p.24: the choice of a suitable maximal compact `K` with `G(𝔸) = P₀(𝔸)K`
  (with references to Tits and to Arthur 1981), fixed before truncation is
  defined.

## `LocalWavePacketInnerProductTruncationCompactStatement`

The data and conclusion of `LocalWavePacketInnerProductStatement`, with every
hypothesis kept (the hypothesis `IsConnectedReductive G` is named `hG`,
because the truncation operator uses it), and four additional hypotheses
about the minimal parabolic `P₀` of the presentation `r`, that is, the
standard minimal parabolic of the maximal split torus `r.data.i` and the
generic cocharacter `r.data.ν`:

- reflection data `D₀ : RelativeRootReflectionData r.data.i` and the
  character comparison `hρ₀` (both are parameters of the truncation operator);
- `P₀(𝔸) K = G(𝔸)`
  (`IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K`);
- for every Siegel setup `(T₀, j)` of `(r.data.i, r.data.ν)`, the parabolic
  part `P₀(𝔸) ∩ K` commutes with the positive torus
  (`AdelicSiegelFactors.IsPositiveTorusCompatible`), as in
  `TruncationOrthogonalProjectionStatement`;
- for some `C` and every truncation parameter `T` with `β(T) > C` for all
  simple roots `β`, the full-quotient truncation with respect to `K`,
  `truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ T`, satisfies
  `IsOrthogonalL2Extension` for `rationalQuotientHaarMeasure F G`.

### Scope of the hypotheses on `K`

The last three hypotheses are what the Lean statement assumes: Iwasawa
coverage for the minimal parabolic, the positive-torus compatibility, and a
supplied `L²` projection for the truncation with respect to the same `K`.
The compact subgroup given by `TruncationOrthogonalProjectionStatement`
satisfies all three. So does a maximal compact subgroup in Lapid's good
position with respect to `M₀` (§2, p.311; Arthur's suitable choice, 2005,
p.24), provided Arthur's Proposition 13.1 holds for it.

The class of compact subgroups allowed here is wider than Lapid's. For
`G = SL₂` over `ℚ`, `P = P' = P₀` the upper Borel subgroup and `M₀` the
diagonal torus, let `K_std` be the standard compact subgroup and
`K = n K_std n⁻¹`, where `n` has real component `[[1,1],[0,1]]` and finite
components `1`. Then `n ∈ P₀(𝔸)`, so `P₀(𝔸)K = G(𝔸)`. The real component of
`P₀(𝔸) ∩ K` is `{±1}`, so the positive-torus condition holds. The truncation
with respect to `K` is the conjugate of the one for `K_std` by the right
translation `R(n)`, which preserves the quotient Haar measure, so the
projection hypothesis holds as well. But the real component of `K` is not
orthogonal to the diagonal for the Killing form, as Arthur's admissibility
relative to `M₀` requires. For such `K`, Lapid's argument does not apply as
written; a transport argument (for example by right translation, as in this
example) is needed to reach a compact subgroup in good position. This module
contains no such argument. In Lapid's proof, `P` and `P'` are moreover
standard for the same minimal parabolic. Here this holds for `P`, and for
`P'` only after conjugation by a rational element.

`LocalWavePacketInnerProductStatement` itself assumes only
`P(𝔸)K = P'(𝔸)K = G(𝔸)`.

## `TruncatedWavePacketLimitStatement`

The data and hypotheses of `LocalWavePacketInnerProductTruncationCompactStatement`,
and any direction `v₀` on which every simple root of `(r.data.i, r.data.ν)` is
positive: the statement quantifies over all such `v₀`. With `Θ`, `Θ'` and `μG` as in `LocalWavePacketInnerProductStatement`,
put `f(y) = Θ(y.out)` and `f'(y) = Θ'(y.out)` on `G(F) \ G(𝔸)`. Let
`trunc j b` be the full-quotient truncation of `b` with respect to `K` at the
parameter `j • v₀`: `b` is pulled back to `G(𝔸)` along `LeftCosetSpace.mk`,
truncated, and evaluated at `q.out`. The conclusion is the conjunction of:

1. `f` and `f'` are measurable and bounded on every compact set;
2. for all large `j`, `trunc j f` and `trunc j f'` are in `L²(μG)`;
3. the real parts of `∫ trunc j f · conj (trunc j f) dμG` and of the same
   integral for `f'` are bounded above for all large `j`;
4. `∫ trunc j f · conj (trunc j f') dμG` tends, as `j → ∞`, to the right side
   of (4) written in the data. This is the same integral over
   `spectralMeasure n` as in `LocalWavePacketInnerProductStatement`.

### Correspondence with Lapid

Item 4 is the convergence that Lapid's sentence asks for. It is asked along
each fixed ray `j • v₀` with `v₀` positive on the simple roots, not along all
of a cone. Lapid's convergence in a cone gives it along every ray in that
cone. Lapid uses items 1–3 without comment:

- `Θ` is smooth, so item 1 holds.
- Item 2 comes from two facts. Truncations of functions of uniform moderate
  growth on `G(F) \ G(𝔸)¹` decrease rapidly (Arthur 2005, Proposition 13.2;
  the Library states this as `ArthurTruncation.TruncationRapidDecayStatement`).
  `Θ` decreases rapidly along `A_G`, because there it is a Fourier transform
  of the smooth compactly supported coefficients.
- Item 3 is item 4 for the pair `(φ, φ)`. It is listed separately because the
  data contain the expansions of `M(w, λ)` only for `Ω(P, P')`, not for
  `Ω(P, P)` or `Ω(P', P')`.

The statement is derived (Lapid, §8). Conversely, given items 1 and 2 and the
projection hypothesis, Proposition 2 implies items 3 and 4. If
`Θ, Θ' ∈ L²`, then `Λ^{j v₀} Θ → Θ` in `L²` by the argument of Lemma 9, so the
truncated inner products converge to `(Θ, Θ')`.

## The theorem `localWavePacketInnerProductTruncationCompact_of_truncatedLimit`

Assume `TruncatedWavePacketLimitStatement` and take the data and hypotheses of
`LocalWavePacketInnerProductTruncationCompactStatement`. The proof uses
`TruncatedWavePacketLimitStatement` for the single direction
`v₀ = 1 ⊗ r.data.ν`, on which every simple root is positive by
`cocharacter_simple_pos`. `r.isCompatible.maximalSplit` and
`r.isCompatible.generic` show that `r.data.i` is a maximal split torus and
`r.data.ν` is generic. `TruncatedWavePacketLimitStatement` gives items 1–4.
Then `ArthurTruncation.fullQuotientTruncationPairing`, with the projection
hypothesis and `ArthurTruncation.truncationFiniteness`, turns them into
`MemLp f 2 μG`, `MemLp f' 2 μG` and `∫ f · conj f' dμG = ` the right side of
(4). The measure `μG` of the conclusion is `rationalQuotientHaarMeasure F G` by
definition: `haarQuotientMeasure` is `discreteQuotientMeasure` of Mathlib's
Haar measure.
