# Direct-rank Laurent spans for the tail of upper induction

Author: Worker 318. Worker 53 contributed the decomposition and the canonical
character/measure interface. The common induction and quantifier conventions
reuse Worker 82's published `InducedTailLFactorStatement`.

This module defines three closed propositions and their conjunction. It proves
none of the span inclusions. All names below are in
`Langlands.RankinSelberg`.

| Proposition | Rank condition | Tail values | Full values |
| --- | --- | --- | --- |
| `InducedTailEqualRankSpanStatement` | `T = B` | Equal-rank values of `(π₂, σ)`, with every Schwartz row test | Zero-row unequal-rank values of `(ξ, σ)` |
| `InducedTailSmallerRankSpanStatement` | `T < B` | Zero-row unequal-rank values of `(π₂, σ)` | Zero-row unequal-rank values of `(ξ, σ)` |
| `InducedTailIntermediateRankSpanStatement` | `B < T < r` | Zero-row unequal-rank values of `(σ, π₂)` | Zero-row unequal-rank values of `(ξ, σ)` |

Each conclusion is `zetaSpan tailValues ≤ zetaSpan fullValues` in
`Submodule LaurentCoefficients RationalFunctions`. Here
`LaurentCoefficients = LaurentPolynomial ℂ`,
`RationalFunctions = RatFunc ℂ`, and the published scalar action sends the
Laurent variable to the rational variable `X = q^(-s)`.
`InducedTailSpanStatement` is the conjunction of the three closed clauses,
in the table's order. In the first name, **EqualRank refers to the tail and
test**, not the full and test; the latter remain unequal in every clause.

## Original source and derived scope

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464.

- Registered source: `jpss-1983-rankin-selberg`.
- Retained PDF: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Section 9.1, printed 452–454 (one-based PDF pages 87–89): the ordered
  upper two-block induction and its Whittaker extension proposition.
- Lemma 9.2, printed 454–455 (PDF 89–90): localization in a lower-block
  chart with arbitrarily small compact open subgroups.
- Lemma 9.3 and its proof, printed 455–457 (PDF 90–92): the three direct
  integral comparisons used here; the final rank-enlargement case on
  printed 457 is outside this module.

The six pages above were read as rendered scans. A bounded local search of
project notes, literature, and Central-Library filenames found no
source-specific erratum. This is not a claim that none exists elsewhere.

The original lemma states a polynomial multiple relation between L-factors
and calls the test representation generic. This module isolates its direct
integral argument as **derived span statements**. It uses the same
Whittaker-type extension of the test representation as the unchanged parent
`InducedTailLFactorStatement`, the Library's canonical coordinates and Haar
normalizations, and independent specified compatible quotient measures.
These choices are not presented as a verbatim statement from JPSS.
The source allows general nonarchimedean local fields; this interface, like
the parent, is restricted to algebraic p-adic fields.

## All quantifiers and normalization

Each clause universally quantifies over every prime `p`, every
`F : PadicField.{uF} p`, every nontrivial continuous unitary additive character
`ψ` for `F.canonicalTopologicalData.topology`, and every supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
Existence of this self-dual measure is not asserted here.
It also quantifies over `a b t : ℕ` with positive ranks
`A = a + 1`, `B = b + 1`, `T = t + 1`, and `r = A + B`.

The three original carriers `V₁ : Type uV₁`, `V₂ : Type uV₂`, and
`W : Type uW` are arbitrary complex modules with additive commutative group
structures. Their universes and the field universe are independent. The
representations `π₁`, `π₂`, and `σ` have ranks `A`, `B`, and `T`, respectively.
The only representation hypotheses are the parent's three
`IsOfWhittakerType` predicates for the **standard** characters of `ψ`.

The full representation `ξ` is literally

```text
F.canonicalNormalizedProductInduced
  (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
  (Shahidi.pairFamily π₁' π₂')
```

where `π₁'` and `π₂'` are the explicit conjugations by
`ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom` on
`ULift.{uV₂} V₁` and `ULift.{uV₁} V₂`. The common block universe is
`max uV₁ uV₂`. These conjugations transport the original actions through
actual linear equivalences; no equivalence is assumed. Tail values always
retain the original `π₂`. The upper parabolic has ordered sizes `(A,B)`;
the modulus on `(g₁,g₂)` is `|det g₁|^B / |det g₂|^A`, and the normalized
induction uses its positive square root. No separately twisted Shahidi
induction is substituted.

After the rank condition, each clause installs the canonical topology,
valuation, local-field instance and Borel measurable structures. It uses
`F.canonicalTopologicalData.residueCardinality` and
`normalizedAbsoluteValue F.canonicalTopologicalData`, so `|ϖ| = q⁻¹`.
The unequal-rank rectangular measure is always the actual product
`rectangularMeasure ν.val 0 (smallRank)`, including its zero-row case.
The supplied additive measure is never replaced by an arbitrary matrix
measure.

The full quotient measure `μfull` is arbitrary on `N_T \ GL_T`. The
independent `μtail` is arbitrary on `N_B \ GL_B` in the equal and
intermediate clauses, and on `N_T \ GL_T` in the smaller clause. Each must
satisfy the full published `QuotientIntegration.IsCompatible` predicate
with `generalLinearHaar` and `unipotentHaar` in its own rank. Thus each is
nonzero and regular, is right invariant, has integrable orbital averages
of continuous compactly supported functions, and satisfies the Weil
integral formula. The ambient and unipotent Haar measures have their
published compact-open integral-subgroup mass-one normalization.
The right-invariance typeclass of each relevant unipotent Haar measure is
universally quantified, as required by `IsCompatible` and the parent's
factor relation. These are measure inputs, not analytic comparison inputs.
Even when the quotient ranks coincide, the two measures are separate
inputs. Relating them by compatible-measure uniqueness or explicit
transport belongs to the proof.

## Actual values and explicit rank transports

The equal-rank tail set is `equalRankZetaValues`, which quantifies over
both actual coefficient Whittaker sets and **all**
`SchwartzBruhat (Fin B → F.Carrier)` row tests. Under `h : t + 1 = b + 1`,
the test action is transported by `(show t = b by omega) ▸ σ` to rank
`b + 1`. This is a type transport; it does not alter the representation.
The tail uses `ψ` on `π₂` and `ψ⁻¹` on the transported `σ`.

Every unequal-rank set is `unequalRankZetaValuesAt 0 k hr`, which transports
the existing `unequalRankZetaValues` along the explicit equation
`largeIndex = smallIndex + (0 + k + 1)`. The indices are ranks minus one:

| Pair | Large index | Small index | `k` |
| --- | --- | --- | --- |
| Full `(ξ, σ)` in every clause | `a + 1 + b` | `t` | `a + 1 + b - t - 1` |
| Tail `(π₂, σ)` for `T < B` | `b` | `t` | `b - t - 1` |
| Tail `(σ, π₂)` for `B < T < r` | `t` | `b` | `t - b - 1` |

The given rank conditions prove these equations by natural-number
arithmetic. The full rank `(a + 1 + b) + 1` is definitionally
`(a + 1) + (b + 1)`, the literal induction rank. The zero row count is
`j = 0` throughout. There is no matrix-coordinate permutation hidden in
these rank equations.

Membership in each value set requires actual coefficient functions,
convergence on a right half-plane, and a rational continuation of their
published integral. Values are not an arbitrary family of rational
functions. No existence of rational continuations, common denominators,
or normalized generators is added as a hypothesis. The result compares
Laurent spans, not individual value sets or polynomials.

## Correspondence with the three source calculations

### Equal tail and test rank: printed 455, final display

For `T=B`, Proposition 9.1 extends any tail coefficient `W₂` and Schwartz
row test `Φ` to a full Whittaker function with restriction
`W(diag(g,1_A)) = W₂(g) Φ(e_B g) |det g|^(A/2)`.
In the full zero-row integral, the exponent `s-(r-T)/2 = s-A/2`
combines with this factor to give `s`, the equal-rank tail exponent.
The bottom display on printed 455 identifies the two integrals for these
functions. Realizing the extension in the actual canonical induced
coefficient set, transporting the equal ranks and compatible measures,
and passing from this identity to rational continuations are proof
obligations. The clause retains every `Φ`; it does not fix one test.

### Smaller test rank: printed 456, first calculation

For `T<B`, the source chooses a Schwartz cutoff `Φ` equal to one wherever
`W₂(diag(g,1_(B-T)))` contributes, referring to §8.3 for the tail support
input. Proposition 9.1 then gives the first displayed integral identity
on printed 456. Combining `|det g|^(A/2)` with the full exponent leaves
`s-(B-T)/2`, the tail zero-row exponent. The successor must prove the
required support/cutoff assertion and extension for the actual coefficient
sets, together with convergence and measure transport. The statement
does not assume the cutoff or a transfer operator.

### Intermediate test rank: printed 456–457

For `B<T<r`, the last part of printed 456 applies Proposition 9.1 and
Lemma 9.2. The latter localizes the extension on the displayed lower-block
chart. In matrix coordinates the lower-left block has `T-B` rows and `B`
columns, and the second diagonal block is lower triangular of size `T-B`.
The proof must establish the corresponding quotient integration formula,
its Jacobian and the measures in these coordinates.

At the top of printed 457, compact open subgroups are chosen small enough
that the test Whittaker function is invariant under the required right
translations. This uses smooth right invariance. Integrating the localized
variables gives a positive, finite, **nonzero volume scalar**. The printed
calculation suppresses it before identifying the reversed tail integral.
The successor must retain and justify the scalar with the actual measures;
a nonzero complex constant is a unit in the Laurent coefficient ring, so
it can be removed at the span level. An appropriate tail-support cutoff
then removes `Φ`, as in the previous case. The resulting determinant
exponent is `s-(T-B)/2`, as in the first integral on printed 457.

There is an additional character issue. The source begins with `W₂` of
character `ψ` on `π₂` and `W'` of character `ψ⁻¹` on `σ`. Its reversed tail
integral is consequently in the larger-first convention for **`ψ⁻¹`**.
Our intermediate clause instead uses the parent's canonical `ψ`: it puts
`ψ` on `σ` and `ψ⁻¹` on `π₂`. These assignments are not identified by
notation. A proof must transport both Whittaker coefficient sets using
the character-change diagonals for the unit `-1`, account for the fixed
right correction in unequal-rank block coordinates, and prove the
associated quotient and rectangular measure changes. Alternatively it
can perform the localization calculation for the inverse character and
transport the full side; that has the same obligations. The normalized
absolute value of `-1` is one, but that fact alone does not replace the
coefficient, integrability or measure-transport arguments.

Relevant published building blocks include
`characterChangeCompatibleMeasure` in `CharacterChangeMeasure`,
`characterChangeRectangularMeasureStatement` in
`RectangularCharacterChangeMeasureProof`, and the coefficient and integral
transports in `UnequalRankCharacterTransport` and
`UnequalRankCharacterIntegrals`. They are possible proof ingredients, not
premises of these propositions or a claim that the needed span bridge is
already proved. If a formal localization route produces a nonzero
rectangular row count, an actual theorem relating that span to the
zero-row span must be proved or applied in the successor. No such span
comparison is inserted as a hypothesis here.

## Analytic and representation-theoretic obligations

For all three cases the displayed identities must first be established on
a common half-plane of convergence, with the actual quotient and product
measures. The successor must prove the required integrability and then use
uniqueness of rational continuation at the canonical `q>1` to transfer the
identity, including any constant multiplier, to `RatFunc ℂ`. Linearity
and closure under Laurent coefficients then give the stated inclusion.
An identity of total Bochner integrals without convergence does not suffice.

`IsOfWhittakerType` retains admissibility, finite generation and the
one-dimensional Whittaker-functional space, as in the parent. It does not
assume an injective coefficient realization or irreducibility. In these
three direct calculations the test representation enters through its
Whittaker coefficient functions; the intermediate calculation additionally
uses their smooth right invariance. Neither step needs irreducibility.
The block hypotheses supply the scope of the 9.1 construction, and 9.2
itself is stated for Whittaker type. Any needed theorem that the canonical
induction is of Whittaker type, and all transports through its ULift
carriers, must be established in the proof chain; they are not extra
hypotheses here.

No clause assumes the desired inclusion, an unspecified comparison map,
a relation of factors, or a normalized factor's existence. No clause covers
`T ≥ r`, Laurent-to-polynomial extraction, or full multiplicativity.
The parent target and all its imported files are unchanged. The present
module imports that published parent only to reuse the same interfaces;
it does not assume its proposition.

## Development validation

The module compiled with no errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Separate declaration inspections
reported `statement_returns_prop: true` for all four definitions and the
independent universe parameters `uF`, `uV₁`, `uV₂`, `uW`. Their only axioms
are the standard `propext`, `Classical.choice`, and `Quot.sound`.
These checks establish well-formed statements, not proofs of the inclusions
or independent semantic acceptance.
