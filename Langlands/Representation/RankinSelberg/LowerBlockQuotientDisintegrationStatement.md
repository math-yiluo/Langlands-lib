# Lower-block disintegration of the actual left unipotent quotient

`Langlands.RankinSelberg.LowerBlockQuotientDisintegrationStatement` states
that every compatible quotient measure on `N_(a+d) \ GL_(a+d)(F)` is a
positive multiple of the pushforward, under the published lower-block chart
`([g], x, h) ↦ [[[g, 0], [x, h]]]`, of an explicit weighted product measure.
The proposition also includes the resulting change-of-variables statements
for integrability and Bochner integrals. The module also defines the
determinant density `D([g]) = |det g|^(-d)` on the small quotient by actual
descent and proves five basic facts about it. The proposition itself is
stated and not proved. A separate proof task is planned.

## Source and provenance

The proposition is derived infrastructure for the displayed integral
calculation in H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
section 9.3, printed pages 456–457 (one-based PDF pages 91–92). The source is
registered as `jpss-1983-rankin-selberg`, kept at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both pages were rendered and read. Section 9.2, printed pages 454–455,
supplies the localization that the source uses on the same pages; that
localization is not part of this proposition. No erratum for this source was
found in the project's literature records. This does not mean that no erratum
exists.

In the case `r₂ < t < r` on printed page 456, the source rewrites
`Ψ(s, W, W'; 0)`, an integral over `g' ∈ N_t\G_t` with weight
`|det g'|^(s-(r-t)/2)` (the same page displays this definition with `r₂` in
place of `r` for the case `t < r₂`), as

```text
∫ W[[g,0,0],[x,h,0],[0,0,1]] W'[[g,0],[x,h]] |det g|^(s+r₂-(r+t)/2) dg d_r(h) dx,
```

"where `g ∈ N_{r₂}\G_{r₂}`, `h ∈ B̄_{t−r₂}`". Here `a = r₂`, `d = t − r₂`,
and `d_r(h)` is a right Haar measure on the lower triangular group `B̄_d`. The
integrand is supported on a compact open subgroup in `h`, where
`|det h| = 1`, so no power of `|det h|` appears. The `|det g|` exponents give
the Jacobian:

```text
(s + r₂ - (r+t)/2) - (s - (r-t)/2) = r₂ - t = -d.
```

So the source's change of variables is `dg' = |det g|^(-d) dg dx d_r(h)`, up
to normalization. On printed page 457 the source continues "up to a positive
constant factor", and it never fixes the constant. The proposition is the
measure-level form of this change of variables, with an explicit constant
`C > 0` and every measure normalization quantified. It is not a verbatim
theorem of the source.

The source calls the parameter space of `x` `M(r₂ × (t − r₂), F)`. However,
the block `x` lies below `g`, so it has `t − r₂` rows and `r₂` columns. As in
the published chart, `x : Matrix (Fin d) (Fin a) F.Carrier` is the displayed
block, with no transpose.

## Ranks

The Library's `generalLinearHaar F n` and `unipotentHaar F n` live on rank
`n + 1`. To use them without casts, the proposition quantifies over all
natural numbers `n` and `k` and sets

```text
a = n + 1,   d = k + 1,   a + d = n + 1 + k + 1.
```

So exactly the positive ranks `a, d ≥ 1` are covered. The rank-`(a+d)`
measures are `generalLinearHaar F.Carrier (n + 1 + k)` and
`unipotentHaar F.Carrier (n + 1 + k)`. `n + 1 + (k + 1)` and
`n + 1 + k + 1` are definitionally equal, so the published chart with
codomain `LeftQuotient (upperUnipotent (n + 1 + (k + 1)) F.Carrier)` is used
directly. The local binding `chart` writes its codomain in the
left-associated form `n + 1 + k + 1`, which every big-rank object in the
statement also uses.

For the consumer `InducedTailIntermediateRankSpanStatement`, with tail rank
`b + 1` and full rank `t + 1` where `b < t`, take `n = b` and `k = t - b - 1`.
After substituting `t = b + 1 + k`, the full rank `t + 1` is literally
`b + 1 + k + 1`.

`Q_m` below is `QuotientIntegration.LeftQuotient (upperUnipotent m F.Carrier)`,
indexed by the actual matrix rank `m`. It equals the Library's
`Quotient (QuotientGroup.rightRel H)`, whose points are the cosets `H * g`, so
`Q_m = N_m \ GL_m`. The published `RankinSelberg.LeftUnipotentQuotient n F`
is `Q_(n+1)`.

## The determinant density

These declarations are in the namespace `Langlands.RankinSelberg`. They work
for any `T : F.TopologicalData` and any natural numbers `m` and `d`.

- `lowerBlockDensity_unipotent_mul`: for `u ∈ upperUnipotent m F.Carrier`,
  the representative weight
  `ENNReal.ofReal (T.normalizedAbs (det (u * g))) ^ (-(d : ℤ))` equals the
  weight of `g`. The proof uses `det (u * g) = det u * det g` and the
  published `unipotent_det` (`det u = 1`).
- `lowerBlockQuotientDensity T m d : Q_m → ℝ≥0∞` is the published
  `QuotientIntegration.descend` of
  `g ↦ ENNReal.ofReal (T.normalizedAbs (det g)) ^ (-(d : ℤ))`, with the
  previous lemma as the invariance proof. So it is defined by actual quotient
  descent, with no chosen representative. `T.normalizedAbs` is the absolute
  value normalized by the residue field cardinality.
- `lowerBlockQuotientDensity_mk` (`simp`, holds by `rfl`): the density of the
  coset of `g` is `ENNReal.ofReal (T.normalizedAbs (det g)) ^ (-(d : ℤ))`.
- `lowerBlockQuotientDensity_ne_top`: the density is never `∞`. By
  `normalizedAbs_eq_zero_iff`, `|det g| > 0` because `det g ≠ 0`, and a
  positive real number's `ENNReal.ofReal` has finite integer powers
  (`ENNReal.zpow_ne_top`).
- `continuous_lowerBlockQuotientDensity`: for `T.topology`, the density is
  continuous on the quotient. The weight on `GL_m` is
  `ENNReal.continuous_zpow` composed with `ENNReal.ofReal`, the coercion from
  `ℝ≥0` and the published continuous homomorphism
  `T.determinantNormContinuous m : GL_m → ℝ≥0ˣ`, whose value at `g` is
  `T.normalizedAbs (det g)`. Then `Continuous.quotient_lift` gives
  continuity on the quotient.
- `measurable_lowerBlockQuotientDensity`: for the Borel structure of the
  quotient topology, the density is measurable because it is continuous.

The proposition uses `D = lowerBlockQuotientDensity F.canonicalTopologicalData
(n + 1) (k + 1)`, so `D([g]) = |det g|^(-d)` on `Q_a` with `d = k + 1`. Its
measurability and finiteness are proved here, as the consumer needs them. No
chart Jacobian, integral comparison or coverage fact is proved or assumed.

## Parameters and structures

The proposition quantifies over every prime `p` (through `[Fact p.Prime]`),
`F : PadicField.{uF} p` in an arbitrary universe `uF`, and `n k : ℕ`. Inside,
the topology, valuation and local-field structure come from the canonical
data `F.canonicalTopologicalData` (`.topology`, `.valuativeRel`,
`.localField`), as in the published `EqualRankEulerStatement`. Borel
measurable structures, with their `BorelSpace` instances, are installed on

- `F.Carrier`;
- `GeneralLinear (n + 1) F.Carrier` and `GeneralLinear (n + 1 + k + 1) F.Carrier`;
- `upperUnipotent (n + 1) F.Carrier` and `upperUnipotent (n + 1 + k + 1) F.Carrier`;
- the quotients `Q_(n+1)` and `Q_(n+1+k+1)`;
- `lowerTriangularSubgroup (k + 1) F.Carrier`.

The matrix space `Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier` keeps Mathlib's
measurable structure on `Matrix`, the iterated product structure of
`Fin (k + 1) → Fin (n + 1) → F.Carrier`. The Library's `rectangularMeasure`
is built on it. The parameter space
`LowerBlockQuotientParameters (n + 1) (k + 1) F.Carrier = Q_a × Matrix × B̄_d`
carries Mathlib's product measurable structure built from these.

After the local bindings below, the proposition quantifies over

- every `η : AdditiveHaarMeasure F.Carrier`, the Library structure of an
  additive Haar measure that is regular, with no normalization;
- the instances `Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` and
  `Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1 + k))`, which
  the compatibility predicate needs in order to be stated (as in the
  published `RecursiveQuotientIntegrationStatement`);
- every `μa : Measure Q_(n+1)` and `μad : Measure Q_(n+1+k+1)` with

```text
IsCompatible (upperUnipotent (n+1) F.Carrier)
  (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μa,
IsCompatible (upperUnipotent (n+1+k+1) F.Carrier)
  (generalLinearHaar F.Carrier (n+1+k)) (unipotentHaar F.Carrier (n+1+k)) μad.
```

`IsCompatible` is the published predicate of `QuotientMeasure`: the measure
is nonzero, regular and right-translation invariant, and satisfies the Weil
formula, with integrability, for continuous compactly supported complex
functions. The two measures are chosen independently. No other hypothesis is
added: in particular no Jacobian, coverage, integral comparison,
representation, Whittaker, L-factor, irreducibility or multiplicativity
hypothesis.

## Local bindings

```text
chart : LowerBlockQuotientParameters (n+1) (k+1) F.Carrier → Q_(n+1+k+1)
  := lowerBlockQuotientChart
D  := lowerBlockQuotientDensity F.canonicalTopologicalData (n+1) (k+1)
dx := rectangularMeasure η (k+1) (n+1)
ν  := (μa.withDensity D).prod (dx.prod ρ)          (written out in Lean)
```

- `chart` is the published descended map of
  `Langlands.Group.GL.LowerBlockQuotientCoordinates`, sending `([g], x, h)` to
  the coset of `lowerBlockPair g x h = [[g, 0], [x, h]]`. It is not rebuilt
  here.
- `dx` is the Library's `rectangularMeasure`, the product of `η.measure` over
  all `(k + 1)(n + 1)` entries of the lower-left block.
- The product is right-associated, `μa × (dx × ρ)`, like the domain of
  `chart`, and the density `D` sits on the first factor `Q_a`.

## Conclusion

For all such data, the proposition asserts the conjunction of

1. `Topology.IsOpenEmbedding chart`: `chart` is a homeomorphism onto its
   range, and the range is open.
2. `Measurable chart`.
3. `μad (Set.range chart)ᶜ = 0`: the range is conull.
4. For every `K : OpenAddSubgroup (Matrix (Fin (k+1)) (Fin (n+1)) F.Carrier)`
   with `IsCompact K`: `0 < dx K` and `dx K < ∞`. (`K` is nonempty, as it
   contains `0`.)
5. There is `ρ : Measure (lowerTriangularSubgroup (k + 1) F.Carrier)` such that
   - `ρ.Regular`, `SigmaFinite ρ`, `ρ.IsOpenPosMeasure` (positive on every
     nonempty open set), `IsFiniteMeasureOnCompacts ρ`, and
     `ρ.IsMulRightInvariant`;
   - for every `K : OpenSubgroup (lowerTriangularSubgroup (k + 1) F.Carrier)`
     with `IsCompact K`: `0 < ρ K` and `ρ K < ∞`;
   - there is a real `C` with `0 < C` and

     ```text
     μad = ENNReal.ofReal C • Measure.map chart ((μa.withDensity D).prod (dx.prod ρ)),
     ```

     and for every Borel measurable `f : Q_(n+1+k+1) → ℂ`,

     ```text
     Integrable f μad ↔ Integrable (f ∘ chart) ((μa.withDensity D).prod (dx.prod ρ)),
     Integrable f μad →
       ∫ q, f q ∂μad = (C : ℂ) * ∫ z, f (chart z) ∂(μa.withDensity D).prod (dx.prod ρ).
     ```

The measure identity is an equality of measures, not only of totalized
integrals. With the measurability of `chart` it gives
`∫⁻ f dμad = ofReal C · ∫⁻ (f ∘ chart) dν` for every nonnegative measurable
`f`, including when both sides are infinite. So consumers can derive absolute
integrability and nonnegative integral identities from it. The integrability
equivalence and the Bochner identity are stated as well, so consumers need
not derive them.

`ρ` and `C` are existential. Since `μad`, `μa` and `η` are all supplied, the
constant `C` absorbs the normalization of `ρ`: rescaling `ρ` by `c > 0`
rescales `C` by `1/c`. No normalization of `ρ` is claimed, and no unproved
normalization is identified with a Library measure. The constant stays
explicit in the identity.

## Why this is the expected convention

This section explains why the statement is expected to hold. It is not part
of the proposition, and its facts are proof obligations of the later proof
task.

Right translation. Let `g₀ ∈ GL_a` and `h₀ ∈ B̄_d`. Then

```text
[[g,0],[x,h]] · diag(g₀, h₀) = [[g g₀, 0], [x g₀, h h₀]],
```

so right multiplication by `diag(g₀, h₀)` acts on the parameters by
`([g], x, h) ↦ ([g g₀], x g₀, h h₀)`. Each of the `d` rows of `x` is
multiplied on the right by `g₀`, and this scales additive Haar measure on a
row by `|det g₀|`. So `dx(S g₀) = |det g₀|^d dx(S)`. The density satisfies
`D([g g₀]) = |det g₀|^(-d) D([g])`, which cancels this factor exactly, while
`μa` is right invariant and `ρ` is right invariant. Also

```text
[[g,0],[x,h]] · [[1,0],[y,1]] = [[g,0],[x + h y, h]],
```

a translation in `x` that preserves `dx`. Since
`[[g,0],[x,h]] = [[1,0],[x g⁻¹,1]] · diag(g, h)`, these two kinds of elements
generate the group `P = {[[g,0],[x,h]] : g ∈ GL_a, h ∈ B̄_d}`. So the
pushforward of the weighted product is invariant under right multiplication
by `P`. The range of `chart` is the right `P`-orbit of the identity coset,
which is isomorphic to `N_a \ P`. The restriction of the right-invariant
measure `μad` to this orbit is also `P`-invariant. Uniqueness of such
invariant measures up to scalars then gives the identity up to the constant
`C`.
For `d ≥ 2` the group `B̄_d` is not unimodular, so a left Haar measure on it is
not right invariant and would fail this test. For `d = 1` (the case `k = 0`,
which the proposition includes) the group is `B̄_1 = GL_1(F) = F×`. It is
abelian, so left and right Haar measures coincide and the right-Haar
convention is still valid. In every rank a nonzero power of `|det h|` in the
density would also fail the test, because right translation by `h₀` would
multiply it by a nonzero power of `|det h₀|`. Both observations agree with the
source's `d_r(h)`.

Rank-two check (`a = d = 1`). Write a matrix in the range as
`[[1,u],[0,1]] · [[g,0],[x,h]] = [[g + u x, u h], [x, h]]`. The additive
measure of the four entries is `|h| du dg dx dh`, and the Haar measure of
`GL_2` is that measure divided by `|det|^2 = |g h|^2`. This gives

```text
du · (dg / |g|) · |g|^(-1) · dx · (dh / |h|),
```

that is, `D(g) d^×g dx d^×h` after removing `du`. This agrees with the
statement: `D = |det g|^(-1)`, the multiplicative Haar measure on the quotient
`Q_1 = GL_1`, additive `dx`, and the multiplicative Haar measure on
`B̄_1 = GL_1`.

Range. A matrix `k = [[K₁₁, K₁₂], [K₂₁, K₂₂]]` has its coset in the range
exactly when `K₂₂ ∈ N_d B̄_d`. If `k = u · [[g,0],[x,h]]` with
`u = [[A,B],[0,E]]`, then `K₂₂ = E h` with `E ∈ N_d`. Conversely, take
`h, E` with `K₂₂ = E h`, `x = E⁻¹ K₂₁`, `B = K₁₂ h⁻¹`, `A = 1`, and let `g` be
the Schur complement `K₁₁ - K₁₂ K₂₂⁻¹ K₂₁`. The Schur complement is invertible
because `det k = det K₂₂ · det g`. `N_d B̄_d` is open in `GL_d`, and its
complement is cut out by vanishing lower-right corner minors. So the range is
open, and its complement is null for Haar measure, hence for `μad`.

## Scope

This module contains one Prop-valued definition, the density definition and
its five lemmas listed above. It proves no disintegration, normalization,
coverage, openness or measurability of the chart. The proposition asserts
these facts and does not assume them. The published `UnipotentQuotient`
construction provides compatible quotient measures in every rank, so the
hypotheses can be satisfied. No existing Library pair is changed.
