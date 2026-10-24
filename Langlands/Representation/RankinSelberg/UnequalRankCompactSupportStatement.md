# Uniform compact support of unequal-rank Whittaker block coefficients

Author: Worker 53.

This module defines the proposition
`Langlands.RankinSelberg.UnequalRankCompactSupportStatement.{uF,uV} F T n j k`.
It states the uniform support assertion used on printed page 393 in the
unequal-rank proof of JPSS Theorem 2.7. It does not prove that assertion.
The imported `AnalyticStatement` supplies the existing representation scope;
the declaration assumes none of its analytic propositions.

## Data and quantifiers

For every prime `p` with `[Fact p.Prime]`, the explicit parameters are
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and arbitrary
natural numbers `n`, `j`, and `k`. The body installs `T.topology`,
`T.valuativeRel`, and `T.localField`. Compactness uses the resulting product
topology on the rectangular matrix space. No equality with the canonical
topological data is imposed.

The proposition quantifies, in order, over:

1. Every `ψ : UnitaryAdditiveCharacter F.Carrier`, the published nontrivial,
   continuous, unitary additive character.
2. Every `V : Type uV`, with every `AddCommGroup V` and `Module ℂ V`
   instance. The universe `uV` is independent of the field universe `uF`.
3. Every complex representation `π` of
   `Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier` on `V`,
   satisfying `IsOfWhittakerType (n + (j + k + 1))
   (standardCharacter ψ (n + (j + k + 1))) π`.
   This means admissibility (which includes smoothness), finite generation
   over the group algebra, and a one-dimensional space of functionals for
   that character. It imposes neither irreducibility nor a unitary central
   character, and does not require `V` to be finite-dimensional over `ℂ`.
4. Every `ℓ : glFunctionals ψ (n + (j + k + 1)) π` with `ℓ.val ≠ 0`,
   and every `f : (coefficientModel π ℓ).toSubmodule`.

For each such `f`, the conclusion chooses a set
`C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier)` and asserts `IsCompact C`.
It then quantifies over all `g : Langlands.GeneralLinear (n + 1) F.Carrier`
and all rectangular matrices `x`, requiring

```lean
f.val.val (unequalRankMatrix j k g x) ≠ 0 → x ∈ C
```

Thus `C` may depend on `f` and all previously fixed data, but is chosen
before `g` and `x`. This is one uniform compact bound, not a separate
compact set for each `g`. The two `.val` projections expose the actual
scalar function from the coefficient-model subtype and the
character-equivariant-function subtype. Such a function has the form
`W(h) = ℓ(π(h)v)` for some `v`; arbitrary scalar functions are not substituted.

There is no quotient measure, Haar normalization, second representation,
spectral parameter, integrability hypothesis, or analytic-existence
hypothesis in the assertion.

## Matrix and rank conventions

In the source's notation, `t = n + 1` is the smaller rank and
`r = n + (j + k + 1) + 1` is the larger rank. Hence
`r - t = j + k + 1`, the source's block index is the same `j`, and its
`k = r - t - 1 - j` is our `k`. Every positive gap and every allowed index
`0 ≤ j ≤ r - t - 1` occurs. In particular, `j = 0`, `k = 0`, smaller rank
one, and gap one (`j = k = 0`) are included without extra hypotheses.

The existing `unequalRankMatrix j k g x` in `QuotientIntegrals` is
`appendIdentity n (j + k + 1) g * rectangularUnipotent j k x`.
Its proved entry formula gives the actual invertible matrix

```text
[g    0     0    ]
[x    I_j   0    ]
[0    0     I_k+1]
```

Here `x` has exactly `j` rows and `t = n + 1` columns. This agrees with
§2.4(3), printed page 387, which writes `x ∈ M(j × t, F)`, and with the
displayed three-block matrix on page 393. The final identity on page 393
has its size suppressed; it is `k + 1` in these parameters.

For comparison with the four-block matrix of Lemma 2.6, put its
`j₁ = t`, its `k = j`, its `j₂ = k`, and its `g₂ = I_k`.
The separate scalar identity in that lemma joins `I_k` to give our final
`I_(k+1)`. The lemma prints `M(j₁ × k, F)` beside a lower-left block that
necessarily has `k` rows and `j₁` columns. That label is reversed relative
to its displayed matrix. The Lean type follows the displayed block and
the explicit `M(j × t, F)` convention of §2.4(3); it does not transpose
`x` or exchange the block parameters.

## Source and scope

Original: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464. Registered source: `jpss-1983-rankin-selberg`, retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The cited scan pages were read visually.

- §2.4(3), printed page 387, supplies the block and dimension convention.
- §2.5, printed pages 388–389, defines gauges and gives the torus expansion
  (2) and finite-sum majorization (3), with Schwartz–Bruhat factors in the
  simple-root coordinates.
- Lemma 2.6, printed pages 389–390, states compact rectangular support for
  a gauge, uniformly in both diagonal group blocks, and a further gauge
  majorization. Its proof bounds simple-root ratios, then bounds the
  rectangular entries through exterior powers of row vectors.
- In the unequal-rank proof of Theorem 2.7, printed page 393, the authors
  explicitly use the consequence that nonvanishing of the displayed
  Whittaker function forces `x` into a compact set independent of `g`.
  Page 394 then uses this to reduce to a finite sum of integrals (7) and
  proceeds to the adjacent-block argument. Those later conclusions are
  separate consumers and are not part of this statement.

This proposition isolates the Whittaker-function consequence at page 393;
it does not restate or prove the full four-block gauge lemma. In §2.5 the
single-gauge majorization is stated with an additional unitary-central-
character hypothesis. That hypothesis is absent from Theorem 2.7's
Whittaker-type scope and from this proposition. A proof in this full scope
must justify the required torus support estimates using §2.5's expansion
or finite-sum majorization, including their applicability to the whole
Whittaker-type scope, and then the geometric support argument of Lemma 2.6.
It cannot apply the unitary-central-character gauge bound to all these
representations without that justification. No such extension, torus
estimate, or compact-support proof is supplied by this statement module.
In particular, importing an unproved canonical-topology asymptotic
statement would not establish the result for the supplied `T`.

## Lean validation

The proposition compiled without errors or warnings in the authorized
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Declaration inspection
reports `statement_returns_prop = true`, independent universe parameters
`uF` and `uV`, and only `propext`, `Classical.choice`, and `Quot.sound`.
This validates the statement's elaboration, not a proof of its assertion.
