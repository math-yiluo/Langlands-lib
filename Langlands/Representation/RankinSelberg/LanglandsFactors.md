# Epsilon factors through square-integrable Langlands data

This module defines and conditionally constructs the epsilon factor of an
arbitrary positive-rank pair through the essentially square-integrable blocks
of genuine Langlands data. The public relation is
`IsLanglandsPairEpsilonFactor.{uF,uV,uW} F ψ ν π σ e`, where
`e = (c,m) : ℂˣ × ℤ` represents `ε(s,π × σ,ψ) = c q^(-ms)`.
The constructor is `langlandsPairEpsilonFactor`. Classification, existence of
block epsilon factors, and independence of the presenting data are explicit
inputs. The module does not prove those analytic or classification results.

## Original source and conventions

Guy Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587–602, Section 2.8, printed
page 596 (PDF page 10, zero-based index 9), identifies the irreducible classes
with finite nonempty multisets of essentially square-integrable classes.
Representatives are ordered by nonincreasing unitary exponent. Their normalized
induction has a unique irreducible quotient, and the final display in Section
2.8 gives the epsilon factor as the product over all pairs of blocks, with the
same additive character in every factor.

Registered source: `henniart-2002-characterization`; retained original:
`/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`.
SHA-256: `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
The original Section 2.8 was read and its rank, ordering, quotient, and product
conventions checked against the implementation. No source erratum was found in
the available project notes.

The implementation uses the Library's `SquareIntegrableLanglandsDatum` with
its positive block sizes, rank sum, irreducible essentially square-integrable
blocks, unitary exponents, and antitone order. Its `IsLanglandsQuotient` is the
actual irreducible-quotient relation for normalized parabolic induction.
The source's classification theorem is not imported as an axiom: the
constructor requires witnesses and an explicit independence proof.
Positive total ranks force the index sets of any such data to be nonempty,
because the sum of an empty block shape is zero. The internal product operation
also has its usual empty-product meaning; no rank-zero representation-level
factor is introduced.

Each block uses the published `IsPadicSymmetricEpsilonFactor`, hence the
integral-based functional-equation relation and larger-rank-first convention
already implemented in `PadicPairFactors`. The rank adapter
`IsPadicRankEpsilonFactor` accepts block sizes that are not syntactically
successors; it reduces to that published relation at positive ranks and to
`False` if either rank is zero. Equal ranks keep their given order. This module
does not prove an exchange theorem for equal ranks.

## Parameters and mathematical content

`F : PadicField.{uF} p` has its canonical topology and residue cardinality `q`.
The coefficient field is `ℂ`. The unitary additive character `ψ` and additive
Haar measure `ν` are explicit, and the same `ψ,ν` are used at every block pair.
The definition accepts an arbitrary such `ν`; any necessary self-duality,
nontriviality, or analytic assumptions belong to proofs of the required block
existence input. There is no assertion that block existence holds for every
choice of these parameters.

The representations have the same carrier-universe shape as the published
nongeneric L relation: `π : SmoothRep.{0,uF,max uF uV} ℂ (GL_(r+1)(F))` and
`σ : SmoothRep.{0,uF,max uF uW} ℂ (GL_(t+1)(F))`. Their block carriers are in
universes `uV` and `uW`, respectively. All positive ranks and both rank orders
are allowed. No irreducibility or admissibility theorem is silently supplied;
the quotient witnesses in the relation entail irreducibility through the
published quotient definition.

`epsilonFactorProduct b` is the pair

`(∏ i, ∏ j, (b i j).1, ∑ i, ∑ j, (b i j).2)`.

The first component is already a complex unit, so the product is nonzero.
The second component is an integer sum. Using the ordinary componentwise
multiplication on `ℂˣ × ℤ` would give the wrong exponent, so that operation is
not used. `epsilonMonomial_factorProduct` proves that for `q > 1` and every
complex `s` this pair evaluates to the product of all the block epsilon
monomials. The spectral point is nonzero, including when an exponent is
negative; there is no exceptional spectral domain for these monomials.

`SquareIntegrableDataEpsilonExistence F ψ ν d d'` says that every pair of
blocks admits an epsilon factor under the published relation.
`IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e` requires an entire family
of such block factors and equality of `e` with its coefficient-product and
exponent-sum pair. `squareIntegrableDataEpsilonFactor` chooses each witnessed
block factor and computes that product, returning it together with a proof
of the relation.

`IsLanglandsPairEpsilonFactor F ψ ν π σ e` requires:

1. Square-integrable Langlands quotient data for `π`.
2. Square-integrable Langlands quotient data for `σ`.
3. For every such pair of data, `IsSquareIntegrableDataEpsilonFactor` holds
   with the same `e`.

The first two clauses prevent a vacuous universal characterization. The third
clause requires actual block factors for every datum pair; a universal
implication whose block-factor premise could always fail would be insufficient.

`LanglandsPairEpsilonBlockExistence` and
`LanglandsPairEpsilonDataIndependence` are proposition-valued inputs. The first
provides block existence for every presenting datum pair. The second says
that the products of any two such datum pairs agree. It does not by itself
assert that any factors exist. `langlandsPairEpsilonFactor` takes these two
inputs and quotient-data witnesses for each representation. It constructs a
product for selected data, constructs products for all other data, and uses
the supplied independence proof to transport their certificates to the
selected product. The result is a subtype containing an actual epsilon pair
and its `IsLanglandsPairEpsilonFactor` proof.

## Implemented proofs and remaining obligations

The rank adapter's uniqueness proof matches on the two positive ranks and
uses `IsPadicSymmetricEpsilonFactor.unique`; the zero-rank cases have no
inhabitants. Fixed-data uniqueness compares block factors pointwise using
this theorem and then substitutes the equal families into their products.
Representation-level uniqueness selects the quotient witnesses from one
certificate and compares both products on those same data. No additional
independence assumption is needed for uniqueness of the defined relation.

The spectral product proof is finite-set induction: the empty case is `1`,
and insertion uses the coefficient product law and the integer-power sum
law at a nonzero spectral point. Applying this identity twice proves the
rectangular product formula. These are intrinsic construction proofs, not
claims to have proved Henniart's classification or analytic factor laws.

The derived formalization packages Henniart's product using the published
data and epsilon relations. It leaves explicit the global existence and
independence obligations, generic compatibility, equivalence-class descent,
and dual, twist, and additive-character transformation laws. In particular,
no compatibility with a tempered standard-module epsilon factor is assumed,
and the published tempered-data L relation is not changed. This module is a
focused construction unit, not completion of the parent harmonic-analysis
and local-factor task.

Worker 31 implemented the module. Worker 7 contributed the consumer-interface
requirements and source/design coordination; no private stand-in definition
was copied.
