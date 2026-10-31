# Nonvanishing of an existing square-integrable pair L-polynomial

Author: Worker 1067.

This module defines the proposition
`Langlands.RankinSelberg.SquareIntegrableLPolynomialNonvanishingStatement.{uF,uV,uW}`.
It is a statement target, not a proof. It keeps the quantifiers and
hypotheses of the published `SquareIntegrablePoleFreeStatement` in
`Langlands.Representation.RankinSelberg.TemperedLFactorStatement` and replaces
only that statement's existential conclusion by a conditional one: every
polynomial satisfying the symmetric pair L-polynomial relation has no zero in
the open unit disk. The module imports `TemperedLFactorStatement` and changes
no published file. It defines no new factor and does not replace the original
target, which remains open.

## Quantifiers and hypotheses

The binders are copied from `SquareIntegrablePoleFreeStatement`, in the same
order:

- every `p : ℕ` with a `Fact p.Prime` instance and every
  `F : PadicField.{uF} p`, with its canonical topological data
  `F.canonicalTopologicalData`;
- every `ψ : UnitaryAdditiveCharacter F.Carrier` for the canonical topology.
  The structure bundles continuity, unit-circle values and nontriviality;
- every `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`,
  a supplied additive Haar measure that is self-dual for `ψ`; the relation
  uses `ν.val`;
- every `r t : ℕ`, every `V : Type uV` and `W : Type uW` in independent
  universes, each with its `AddCommGroup` and `Module ℂ` structure;
- every actual representation
  `π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V` and
  `σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W`;
- the four hypotheses `Representation.IsIrreducible π`,
  `F.canonicalTopologicalData.IsSquareIntegrable π`,
  `Representation.IsIrreducible σ` and
  `F.canonicalTopologicalData.IsSquareIntegrable σ`.

`IsSquareIntegrable` is the unchanged published analytic predicate of
`Classification.Tempered`, taken modulo the center: for every Borel Haar
measure on the actual quotient of the general linear group by its center,
`IsSquareIntegrableModCenter` holds. That is admissibility, a unitary central
character, and square-integrable norms of all smooth matrix coefficients
modulo the center. It is not replaced by a segment or classification
condition. No genericity, Whittaker-type, convergence, holomorphy or
factor-existence hypothesis is added.

## Conclusion

The conclusion is

```lean
∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
  ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0
```

Both rank orders use the existing symmetric relation
`IsPadicSymmetricLPolynomial` of `PadicPairFactors`: when `t ≤ r` it is
`IsPadicPairLPolynomial F ψ ν.val π σ P`, and when `r < t` it is
`IsPadicPairLPolynomial F ψ ν.val σ π P`, following the JPSS (2.12)
convention that a pair is read with the larger rank first. Equal ranks are
included. The relation requires that a compatible quotient measure exists and
that `P` is the published pair L-polynomial for every compatible quotient
measure.

Since `L(s, π × σ) = 1/P(q^(-s))` and `Re(s) > 0` exactly when
`‖q^(-s)‖ < 1`, the conclusion says that this L-factor has no pole in the
half-plane `Re(s) > 0` (see the "Poles" paragraph of
`TemperedLFactorStatement.md`). The point `z = 0` is included; a normalized
L-polynomial has constant term `1`.

## Relation to the existential statement

`SquareIntegrablePoleFreeStatement` asserts that some `P` satisfies the
relation and has no zero with `‖z‖ < 1`. This proposition asserts only the
second part, for every `P` satisfying the relation. Because the relation has
at most one solution (`IsPadicSymmetricLPolynomial.unique`), the existential
statement is equivalent to this proposition together with existence of the
polynomial. That equivalence is not proved in this module.

Existence of the polynomial remains a separate substantive obligation: it
needs the normalized generators of JPSS Theorem 2.7 for the pair, for every
compatible quotient measure. This proposition neither asserts nor assumes
it. For a pair with no such polynomial the conclusion holds vacuously, so the
proposition alone does not prove the original target.

## Provenance

This is an internal statement derived from the Library's
`SquareIntegrablePoleFreeStatement`. That statement's paired Markdown,
`TemperedLFactorStatement.md`, gives its source: JPSS 1983, display (6) in
the proof of Theorem (8.2), printed page 445 (registered source
`jpss-1983-rankin-selberg`), which says that the L-factor of two
square-integrable representations has no pole in `Re(s) > 0`. JPSS do not
state the conditional formulation of this module separately; it isolates the
nonvanishing half of the Library's existential formulation. This module makes
no new literature attribution.

The intended implication assembles published results; it is described here
and is not proved in this module:

1. The existence component of `IsPadicPairLPolynomial` supplies a compatible
   quotient measure, for which `P` is the normalized generator of the
   intrinsic zeta-value sets. These sets range over all Whittaker functionals
   of the two representations (`whittakerSet`, `inverseWhittakerSet`), all
   vectors of their coefficient models and, in equal rank, all
   Schwartz–Bruhat functions.
2. In equal rank, `squareIntegrableEqualRankAnalytic` (module
   `SquareIntegrableEqualRankAnalyticProof`) gives convergence and holomorphy
   of the coefficient-model integrals on `Re(s) > 0`. In unequal rank, the
   generator of the pair relation generates the values of every block,
   including the block `j = 0`, and `squareIntegrableZeroRowAnalytic`
   (module `SquareIntegrableZeroRowAnalyticProof`) gives the same conclusion
   for that block. No new rationality or common-generator theorem is needed.
3. `holomorphicRationalContinuation` turns holomorphy on `Re(s) > 0` into
   regularity of each rational continuation on the punctured unit disk.
4. `IsNormalizedGenerator.eval_ne_zero_of_regularAt`, the content of
   `normalizedGeneratorRegularity` (module `NormalizedGeneratorRegularityProof`),
   excludes a zero of `P` at each `z` with `0 < ‖z‖ < 1`, and
   `IsNormalizedGenerator.eval_zero_ne_zero` excludes `z = 0`.

This route constructs no generator and proves no genericity or multiplicity
one.

## Lean checks

The module compiles with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings. Inspection
of `SquareIntegrableLPolynomialNonvanishingStatement` reports that it is a
definition returning `Prop`, with universe parameters `uF uV uW`, using only
`propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no new
axiom.
