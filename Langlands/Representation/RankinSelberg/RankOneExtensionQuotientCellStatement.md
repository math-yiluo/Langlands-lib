# The rank `t + 2` unipotent quotient in lower-block coordinates

Authors: Worker 802 (draft), Worker 835.

`Langlands.RankinSelberg.RankOneExtensionQuotientCellStatement.{uF}` is a
closed proposition definition. It states that every compatible quotient
measure on `N_(t+2) \ GL_(t+2)(F)` is a positive finite multiple of an
explicit pushforward built from any compatible quotient measure on
`N_(t+1) \ GL_(t+1)(F)`, the row variable and the scalar unit. This module
supplies no proof.

## Quantifiers and conventions

The proposition quantifies over every prime `p`, every `F : PadicField.{uF} p`
and every `t : ℕ` (including `t = 0`). It installs exactly the topology,
valuative relation and local-field certificate of `F.canonicalTopologicalData`
and the Borel σ-algebras, with `BorelSpace` certificates, of `F.Carrier`,
`F.Carrierˣ`, `GeneralLinear (t + 1) F.Carrier`, `upperUnipotent (t + 1)`,
`LeftUnipotentQuotient t`, `GeneralLinear ((1 + t) + 1) F.Carrier`,
`upperUnipotent ((1 + t) + 1)` and `LeftUnipotentQuotient (1 + t)` (quotient
topologies on the quotients). Apart from the added Borel σ-algebra on
`F.Carrierˣ`, which `localMultiplicativeHaar` needs, this is literally the
instance stack of
`Langlands.RankinSelberg.RankOneExtensionSpanComparisonStatement`.

It then quantifies over:

- right-invariance certificates
  `Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)` and
  `Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))`, required by
  the published predicate `QuotientIntegration.IsCompatible` (the same
  premises as in the span-comparison statement);
- every `μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier`;
- every `μbase` on `LeftUnipotentQuotient t F.Carrier` with
  `IsCompatible (upperUnipotent (t + 1) F.Carrier) (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase`;
- every `μind` on `LeftUnipotentQuotient (1 + t) F.Carrier` with
  `IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier) (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind`.

`IsCompatible` says that the measure is nonzero, regular and right invariant,
that the orbit averages of compactly supported continuous complex functions
`f` are integrable, and that the Weil formula
`∫_{N\G} (∫_N f(n g) dn) dq = ∫_G f` holds for every such `f`. Here `N\G` is
the quotient by left multiplication by `N`. The two quotient measures are
independent.

## Exact conclusion

Write `B(m, x, a)` for the published `rankOneExtensionLowerBlock t m x a`, the
matrix `[m, 0; x, a]` with `m : GL_(t+1)` in the first `t + 1` rows and
columns, the unscaled row `x : Fin (t + 1) → F.Carrier` in the last row, and
the unit `a` in the last diagonal entry. Its published type is
`GeneralLinear (1 + (t + 1)) F.Carrier`. The statement uses it in
`GeneralLinear ((1 + t) + 1) F.Carrier`, the ambient rank of `μind`. The two
ranks are definitionally equal, so no cast or reindexing is involved.

There is `c : ℝ≥0∞` with `c ≠ 0` and `c ≠ ⊤` such that

`μind = c • map Ψ ((μbase × (rowMeasure μ (t + 1) × localMultiplicativeHaar F.Carrier)).withDensity ρ)`,

where

- `Ψ (q, x, a) = N_(t+2) · B(Quotient.out q, x, a)` is the class in
  `LeftUnipotentQuotient (1 + t) F.Carrier`;
- `ρ (q, x, a) = |det (Quotient.out q)|⁻¹` is the inverse in `ℝ≥0∞` of the
  published normalized absolute value
  `F.canonicalTopologicalData.normalizedAbsHom`, coerced from `ℝ≥0`. Since
  the determinant is nonzero, `ρ` takes finite positive values;
- `rowMeasure μ (t + 1)` is the product measure `dx` on rows, and
  `localMultiplicativeHaar F.Carrier` is the published multiplicative Haar
  measure `d^×a` on `F.Carrierˣ`.

The product is `μbase × (dx × d^×a)`, with Lean's right-nested product.
Equivalently, for every measurable `H : LeftUnipotentQuotient (1 + t) F.Carrier → ℝ≥0∞`,

`∫⁻ H dμind = c ∫_{N_(t+1)\GL_(t+1)} ∫_x ∫_a H(N_(t+2) B(m, x, a)) |det m|⁻¹ d^×a dx dμbase(m)`.

This uses the measurability of `Ψ` and `ρ` (see below) and Tonelli's theorem.

### Representative independence

`Quotient.out q` only serves to write `Ψ` and `ρ` without proof terms.
Neither depends on the representative. Two representatives of `q` differ by
left multiplication by some `n` in the upper unipotent subgroup of
`GL_(t+1)`. Then `B(n m, x, a) = diag(n, 1) B(m, x, a)`, where `diag(n, 1)` is
upper unipotent in `GL_(t+2)`, and `det (n m) = det m`. So `Ψ` and `ρ` are the
descents of the continuous maps `(g, x, a) ↦ N_(t+2) B(g, x, a)` and
`(g, x, a) ↦ |det g|⁻¹` along the open quotient map. Both are therefore
continuous. All factors are second countable, so they are measurable for the
product σ-algebra. In particular, `Measure.map Ψ` is the genuine pushforward.
An equivalent formulation would use these descended maps instead of
`Quotient.out`.

No normalization is imposed. The constant `c` depends on `μ`, `μbase`, `μind`
and the published Haar normalizations.

## Provenance

The source is JPSS (1983), Lemma (5.5), registered as
`jpss-1983-rankin-selberg`. The lemma is stated on printed p. 423 and proved
on printed pp. 424–427 (PDF pages 58–62). That proof works in the lower
parabolic coordinates. On printed p. 425 a point `q` of the lower parabolic is
written as `[1, 0; y, 1][m, 0; 0, a]` with right Haar measure `d_r(q)`.
Display (8) on printed p. 426 integrates against `[m, 0; x, a]`, with `m`
modulo the unipotent subgroup, using `dm d^×a dx`. The source does not display
a decomposition of the quotient measure. In the source, the rank `t` of `G_t`
corresponds to `(1 + t) + 1` here, and `t₁` to `t + 1`.

The present formula is a derived, internal statement that makes this
decomposition explicit for the strict Lemma (5.5) argument. It is expected to
follow from three ingredients:

- On the open cell `u(y) B(m, x, a)`, with `u(y) = [1, y; 0, 1]`, Haar measure
  on `GL_(t+2)` is a positive multiple of `dy |det m|⁻¹ dm dx d^×a`. Here
  `|det m|⁻¹ dm dx d^×a` is a right Haar measure on the lower parabolic.
- The upper unipotent subgroup of `GL_(t+2)` is `u(y) diag(n, 1)`, with Haar
  measure `dy dn`.
- The Weil formula for `μbase` gives the result, together with uniqueness of
  compatible quotient measures up to a positive scalar.

These are not proved here.

The published `Langlands.RankinSelberg.LowerBlockQuotientDisintegrationStatement`
is a general-block-size analogue. It uses the chart
`([g], x, h) ↦ [[g, 0], [x, h]]` with `h` in the lower-triangular group and an
existential right Haar measure on that group. It uses the ambient rank
`n + 1 + k + 1`, which is not definitionally `(1 + t) + 1`. Its density
`|det g|^(-d)` agrees with `ρ` when `d = 1`. The present statement is
independent of it. It is written in the ranks, matrices and measures of
`RankOneExtensionSpanComparisonStatement` and `RankOneExtensionAnalyticData`,
so that the consumer can apply it directly.
