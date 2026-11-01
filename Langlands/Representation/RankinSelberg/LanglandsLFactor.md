# Constructing nongeneric L-factors through tempered Langlands data

Author: Worker 31.

This module constructs a polynomial certified by the existing
`RankinSelberg.IsLanglandsPairLPolynomial` relation, and the actual rational
unit `1 / P(X)` from any such certified polynomial. Its classification,
exhaustion and analytic existence inputs are explicit. It does not prove those
inputs or change the definition of the nongeneric L-factor.

## Provenance and dependencies

This is a derived construction from published Library interfaces:

- `RankinSelberg/LanglandsQuotientLFactorStatement` supplies
  `IsLanglandsPairLPolynomial`, its uniqueness theorem, and
  `LanglandsTypeLFactorStatement`.
- `Classification/RegularLanglandsStatement` supplies the proposition
  definitions `GLRegularLanglandsDataUniquenessStatement` and
  `GLRegularLanglandsExhaustionStatement`. They remain hypotheses here.
- `Classification/LanglandsData` supplies genuine tempered block data,
  normalized upper-parabolic standard modules, actual quotient maps and
  `twistedProductInducedIso`.
- `RankinSelberg/PadicPairFactors` supplies invariance of the integral-based
  L-polynomial under representation equivalence.
- `RankinSelberg/PadicPairLPolynomialNormalization` supplies constant-term
  normalization of the p-adic pair and symmetric polynomial certificates,
  using the generator normalization from `RankinSelberg/PairLFactor`.
  Mathlib supplies finite order-isomorphism rigidity
  and the polynomial embedding into rational functions.

The inherited definition is JPSS, *Rankin-Selberg convolutions* (1983),
§9.4, printed p.458, especially display (4) and the paragraph defining the
L-factor for every irreducible admissible pair. The original page image was
read: it uses tempered blocks with strictly decreasing real exponents and
defines the factor through their standard modules. The source and its
normalizations are documented in the imported
`LanglandsQuotientLFactorStatement.md`; the source SHA256 is
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The regular classification propositions have their separate Silberger and
Kudla provenance in `RegularLanglandsStatement.md`.

The new content is the internal deduction from these interfaces: ordered
matching gives an isomorphism of actual standard modules; equivalence
invariance transports one polynomial certificate to every presentation.
Classical choice is applied only to supplied existence proofs. The unit
construction is algebraic inversion of a proved nonzero polynomial.
No new assertion from the literature is introduced as an axiom.

## Parameters and normalization

The field is `F : PadicField.{uF} p`, with its canonical topology and
residue-normalized absolute value. The character is the existing nontrivial
unitary additive character `ψ`, and `ν` is an additive Haar measure.
The construction itself does not assume self-duality; its analytic
existence input concerns this precise measure. The bridge from
`LanglandsTypeLFactorStatement` uses a self-dual Haar measure, as required by
that imported statement.

The two ranks are independently `r + 1` and `t + 1`, covering all positive
ranks, including rank one and both rank orders. The imported symmetric
relation reads the larger rank first and retains the given order when ranks
are equal. The polynomial satisfies `P.coeff 0 = 1`. The rational unit has
value `1 / P(X)` with spectral convention `X = q^(-s)`. No claim about total
evaluation at a pole is made.

The polynomial normalization lemmas and `langlandsPairLFactor` retain the
original relation's block universes `uV` and `uW`. The classification
constructors use blocks in `max uF uV` and `max uF uW`, respectively, because
the imported regular classification propositions have exactly that scope.
The result is explicitly
`IsLanglandsPairLPolynomial.{uF, max uF uV, max uF uW}`. This does not assert
that blocks can be lowered to `uV` or `uW`.

## Implemented construction

`TemperedLanglandsDatum.nonempty_standardModule_iso_of_matching` is in
`Langlands.PadicField.TopologicalData`. Given an order isomorphism of block
index sets, matching block ranks, equal exponents and actual block
isomorphisms after rank transport, it proves that the standard modules are
isomorphic. The proof compares finite cardinalities, uses
`Fin.coe_orderIso_apply` to identify the order isomorphism with the identity,
and eliminates the resulting equalities of size and exponent functions.
The remaining block isomorphisms feed the published
`twistedProductInducedIso`. Thus no arbitrary permutation of induced blocks
is treated as an equality or an isomorphism.

The remaining names are in `Langlands.RankinSelberg`:

- The imported `IsPadicPairLPolynomial.coeff_zero` extracts an actual
  compatible quotient measure from the relation and invokes the underlying
  pair-polynomial normalization. The imported
  `IsPadicSymmetricLPolynomial.coeff_zero` follows by the two rank-order
  branches. These lemmas are in `PadicPairLPolynomialNormalization`.
- `IsLanglandsPairLPolynomial.coeff_zero` uses the relation's presenting
  witnesses and its universal standard-module certificate.
  `IsLanglandsPairLPolynomial.ne_zero` follows because the constant
  coefficient is one.
- `langlandsPairLFactor` takes the subtype of certified polynomials and
  returns a unit in `RationalFunctions`. It forms the polynomial's image
  under `algebraMap`, proves this image nonzero, and inverts the resulting
  unit. `coe_langlandsPairLFactor` gives its exact value.
  `langlandsPairLFactor_eq` proves independence of the certified polynomial
  witness using the imported uniqueness theorem.
- `LanglandsStandardLPolynomialExistence` is the remaining analytic
  proposition: for every datum pair presenting the given representations,
  some polynomial satisfies the existing integral-based symmetric relation
  for their standard modules. It assumes no agreement across presentations.
  The theorem
  `LanglandsTypeLFactorStatement.standardLPolynomialExistence` supplies this
  input from a proof of the imported JPSS standard-module product statement
  by retaining its polynomial and first certificate. It does not prove
  that statement or its product formula.
- `standardModule_iso_of_regular_uniqueness` applies the regular
  ordered-data uniqueness input to two quotient presentations and the
  identity isomorphism of their common quotient, then uses the matching
  lemma.
- `langlandsPairLPolynomialOfData` starts with two actual quotient data and
  existence of a polynomial for just their standard modules. It chooses
  that polynomial, retains the presenting witnesses, and proves the
  certificate for every other datum pair by the two standard-module
  isomorphisms and the published equivalence invariance theorem.
- `langlandsPairLPolynomialOfClassification` applies the two exhaustion
  inputs to the irreducible admissible representations, obtains head data,
  and converts head witnesses to quotient witnesses. Its explicit analytic
  input gives a polynomial for these standard modules, and the preceding
  constructor supplies the full certificate.

Applying `langlandsPairLFactor` to the result of either polynomial
constructor gives the corresponding rational L-unit.

## Remaining obligations

Regular classification and exhaustion, and the analytic existence of the
standard-module L-polynomial, are not proved here. The last analytic input
can be supplied by the existing `LanglandsTypeLFactorStatement`, once proved
at the required universes with self-dual measure. The imported integral
relation retains quotient-measure existence, rationality and normalized
generator requirements; it is not replaced by an arbitrary factor function.

This module does not prove the generic-quotient comparison, the
square-integrable block-product law, a twist or character-change law, or any
statement about epsilon or gamma factors. Those remain separate existing
responsibilities. The module is a conditional construction within the
larger harmonic-analysis task, not completion of that task.
