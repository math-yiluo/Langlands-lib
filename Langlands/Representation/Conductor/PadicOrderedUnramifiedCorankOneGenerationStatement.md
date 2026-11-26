# Generation by corank-one integrals of `π × I(x)` for norm-ordered `x`, over p-adic fields

This module, in namespace `Langlands.Conductor`, defines one proposition,
`PadicOrderedUnramifiedCorankOneGenerationStatement`, with universe parameters `uF uV`.
It proves nothing.

The proposition is the published
`Langlands.Conductor.OrderedUnramifiedCorankOneGenerationStatement`
([`OrderedUnramifiedCorankOneGenerationStatement`](OrderedUnramifiedCorankOneGenerationStatement.md))
with one change. The field is the carrier `K.Carrier` of a p-adic field
`K : PadicField.{uF} p` (a finite extension of `ℚ_p`, for a prime `p`). It carries its
canonical topology, valuation and local-field structure, and it replaces an arbitrary
nonarchimedean local field. The binders after the field and the conclusion are the same.

## The statement

`PadicOrderedUnramifiedCorankOneGenerationStatement` quantifies over a prime `p` (with
`[Fact p.Prime]`) and a p-adic field `K : PadicField.{uF} p`. Through `letI` it gives
`K.Carrier` three structures from `K.canonicalTopologicalData` (module
`Langlands.LocalField.Canonical`): the topology, the valuative relation and the
`IsNonarchimedeanLocalField` structure. This is the convention of
[`PadicSphericalLFactorGenerationStatement`](PadicSphericalLFactorGenerationStatement.md).

The remaining binders are those of `OrderedUnramifiedCorankOneGenerationStatement` at
`F = K.Carrier`, in the same order:

- `n`, the measurable and Borel structures, `q`, `ψ`, `abv`, `ϖ`, `μ` and
  `h : IsJacquetNormalization q ψ abv ϖ μ`;
- `V : Type uV`, a representation `π` of `GL_(n+2)(K)` on `V` with
  `IsGeneric ψ (n + 1) π`, and `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`;
- `P : ℂ[X]` with `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar K.Carrier) 1 π P`
  (`L(s, π × 1) = P(q^(-s))⁻¹`, `P(0) = 1`);
- `x : Fin (n + 1) → ℂˣ` with `Monotone (fun i => ‖(x i : ℂ)‖)`, that is,
  `|x_1| ≤ ⋯ ≤ |x_(n+1)|`;
- `ℓ' : glInverseFunctionals ψ n ρ` with `ℓ'.val ≠ 0`. Here
  `ρ = principalSeries h.uniformizer n h.residueCardinality x` is the normalized
  unramified principal series `I(x)` of `GL_(n+1)(K)`
  ([`UnramifiedPrincipalSeries`](UnramifiedPrincipalSeries.md)), and `ℓ'` is a
  Whittaker functional for the inverse character `ψ̄`.

Write `Ψ(s, W, W')` for `corankOneIntegral ψ abv μ W W' s`, `X = q^(-s)` for
`spectralPoint q s`, and `Q_x = ∏ i, P.comp (C (x i) * X)`. The conclusion: there are
`k : ℕ`, `W : Fin k → coefficientModel π ℓ`, `W' : Fin k → coefficientModel ρ ℓ'` and
`a : ℝ` with `(∑_j Ψ(s, W_j, W'_j)) · Q_x(q^(-s)) = 1` for every `s` with `a < Re s`.
With `x_i = q^(-t_i)`, this says `∑_j Ψ(s, W_j, W'_j) = ∏_i L(s + t_i, π)` on a right
half-plane.

The source correspondence is that of
[`OrderedUnramifiedCorankOneGenerationStatement`](OrderedUnramifiedCorankOneGenerationStatement.md):
Jacquet 2012, Lemma 3, printed page 519 (literature ID
`jacquet-2012-conductor-correction`), quoted from JPSS 1983, Section 9 (literature ID
`jpss-1983-rankin-selberg`). It applies word for word with `F = K.Carrier`.

## Relation to the general statement

`OrderedUnramifiedCorankOneGenerationStatement` implies this proposition: instantiate
its field at `K.Carrier` with the canonical structures. The converse is not claimed.

Over p-adic fields it plays the role that the general statement plays in the published
reduction `sphericalLFactorGeneration_of_ordered`: Jacquet's Lemma 3, from which
[`PadicSphericalLFactorGenerationStatement`](PadicSphericalLFactorGenerationStatement.md)
follows by his Lemmas 1, 2 and 4. In JPSS 1983 the identity follows from the computation
of `L(s, π × I(x))` in Section 9. That computation uses:

- the Langlands classification of `π`, with the equality of the Whittaker models of `π`
  and of its standard module;
- the tempered pole bound (8.4);
- the tail divisibility (9.3);
- the double induction of (9.4).

The Library's theorems for the first three are stated over p-adic fields, as listed in
[`PadicSphericalLFactorGenerationStatement`](PadicSphericalLFactorGenerationStatement.md).

## Imports

- `Langlands.LocalField.Canonical`;
- `Langlands.Representation.Conductor.OrderedUnramifiedCorankOneGenerationStatement`,
  whose import closure supplies every other name used, including `principalSeries`,
  `glInverseFunctionals` and `coefficientModel`.
