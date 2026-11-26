# The L-factor facts behind the existence of the essential vector, over p-adic fields

This module, in namespace `Langlands.Conductor`, defines one proposition,
`PadicSphericalLFactorGenerationStatement`, with universe parameters `uF uV`.
It proves nothing.

The proposition is the published `Langlands.Conductor.SphericalLFactorGenerationStatement`
([`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md)) with one
change. The field is the carrier `K.Carrier` of a p-adic field `K : PadicField.{uF} p`
(a finite extension of `ℚ_p`, for a prime `p`). It carries its canonical topology,
valuation and local-field structure, and it replaces an arbitrary nonarchimedean local
field. Everything else is the same:

- the binders after the field;
- Jacquet's normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`;
- the representation `π`, with `IsGeneric ψ (n + 1) π`, and the functional `ℓ`;
- the three clauses of the conclusion.

## The statement

`PadicSphericalLFactorGenerationStatement` quantifies over a prime `p` (with
`[Fact p.Prime]`) and a p-adic field `K : PadicField.{uF} p`. Through `letI` it gives
`K.Carrier` three structures from `K.canonicalTopologicalData` (module
`Langlands.LocalField.Canonical`): the topology, the valuative relation and the
`IsNonarchimedeanLocalField` structure. The published
`SupercuspidalPadicConductorExponentStatement` and the Library's other p-adic statements
follow the same convention.

With these structures, the remaining binders are those of
`SphericalLFactorGenerationStatement` at `F = K.Carrier`, in the same order:

- `n : ℕ`;
- measurable and Borel structures on `GL_(n+1)(K)`, its upper unipotent subgroup, the
  quotients `LeftUnipotentQuotient n K.Carrier` and `LeftUnipotentQuotient 0 K.Carrier`,
  and `GL_1(K)`;
- `q`, `ψ`, `abv`, `ϖ`, `μ` and `h : IsJacquetNormalization q ψ abv ϖ μ`;
- `V : Type uV` and `π : Representation ℂ (GeneralLinear ((n + 1) + 1) K.Carrier) V`
  with `IsGeneric ψ (n + 1) π`;
- `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`.

Write `W_x` for `inverseSphericalWhittaker h.conductor.1 h.uniformizer q x`, Jacquet's
`W(g; x; ψ̄)`, and `Ψ(s, w, W_x)` for `corankOneIntegral ψ abv μ w W_x s`. Write
`X = q^(-s)` for `spectralPoint q s` and `Q_x = ∏ i, P.comp (C (x i) * X)`.

The conclusion is that there is `P : ℂ[X]` with
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar K.Carrier) 1 π P`, that is,
`L(s, π × 1) = P(q^(-s))⁻¹` with `P(0) = 1`, such that the following hold.

1. **Convergence.** For every `w` in `coefficientModel π ℓ` and every
   `x : Fin (n + 1) → ℂˣ`, `CorankOneConverges ψ abv μ w W_x s` holds for `s` in a
   right half-plane.
2. **Laurent numerator.** For every `w` and `x` there are `a`, `N : ℤ` and `Q : ℂ[X]`
   with `Ψ(s, w, W_x) · Q_x(q^(-s)) = q^(-Ns) Q(q^(-s))` for `a < Re s`.
3. **Generation (Jacquet's Lemma 4).** For every `x` there are `k`, vectors
   `W : Fin k → coefficientModel π ℓ`, integers `e : Fin k → ℤ` and `a` with
   `(∑_j q^(-e_j s) Ψ(s, W_j, W_x)) · Q_x(q^(-s)) = 1` for `a < Re s`.

The explanations of the clauses, of the JPSS polynomial `P` (as opposed to
Godement–Jacquet's) and of the source correspondence are those of
[`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md). They
apply word for word with `F = K.Carrier`.

## Relation to the general statement

`SphericalLFactorGenerationStatement` implies this proposition: instantiate its field at
`K.Carrier` with the canonical structures. The converse is not claimed. Over a field of
positive characteristic the present proposition says nothing.

Jacquet's argument (section 1, Lemma 3) rests on four results of JPSS 1983:

- the Langlands classification of generic representations, with the equality of the
  Whittaker models of `π` and of its standard module;
- the tempered pole bound (8.4);
- the tail divisibility (9.3);
- the double induction of (9.4).

The Library's theorems for these results are stated for representations of `GL_n(K)`
with `K` a p-adic field:

- `Classification.temperedLanglandsQuotientCoverage`;
- `RankinSelberg.genericLanglandsQuotientLFactor`;
- `RankinSelberg.analyticTemperedTwistLPolynomial_poleFree`;
- `RankinSelberg.inducedTailLFactor`;
- `RankinSelberg.langlandsTypeLFactor`.

The present proposition is the case of the general statement that these theorems reach.

## Source

H. Jacquet, *A correction to Conducteur des représentations du groupe linéaire*,
Pacific J. Math. 260 (2012), 515–525, literature ID
`jacquet-2012-conductor-correction`, section 1, printed pages 517–519. Jacquet works
over an arbitrary nonarchimedean local field. A p-adic field is a special case.

## Imports

- `Langlands.LocalField.Canonical`: the canonical topology, valuation and local-field
  structure.
- `Langlands.Representation.Conductor.SphericalLFactorGenerationStatement`, whose import
  closure supplies the other names used: `IsJacquetNormalization`,
  `IsCharacterLPolynomial`, `rankOneQuotientHaar`, `CorankOneConverges`,
  `corankOneIntegral`, `inverseSphericalWhittaker` and `spectralPoint`.
