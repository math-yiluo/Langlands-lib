# Pole-freeness of square-integrable Rankin–Selberg L-factors

Authors: Worker 192, with Worker 1067 contributing the exact wrapper binder
pattern reused from the nonvanishing proof.

`Langlands.RankinSelberg.squareIntegrablePoleFree` proves exactly
`Langlands.RankinSelberg.SquareIntegrablePoleFreeStatement.{uF,uV,uW}`
from `Langlands.Representation.RankinSelberg.TemperedLFactorStatement`.
For every irreducible analytically square-integrable pair of positive-rank
general linear representations, it constructs a polynomial satisfying
`IsPadicSymmetricLPolynomial` and proves that its value is nonzero at every
complex point of norm less than one.

The theorem preserves independent field and carrier universes, every prime
and canonical p-adic field, every allowed continuous nontrivial unitary
additive character, the supplied self-dual additive Haar measure, rank one
and both rank orders. The original representations and their actual
analytic square-integrability modulo the full center are retained. There
are no additional genericity, unitarizability, factor-existence, convergence
or support hypotheses.

## Implemented proof

The proof introduces the exact quantifiers and hypotheses of the published
target. For the first representation it applies
`Classification.squareIntegrableGenericity.{uF,uV}` at
`F.canonicalTopologicalData`, then supplies that proved proposition to
`squareIntegrableWhittakerType_of_genericity.{uF,uV}`. It does the same for
the second representation in the independent universe `uW`.

The latter published bridge derives admissibility from analytic
square-integrability and derives an invariant positive Hermitian form from
`glSquareIntegrableUnitarity`. It bundles the original smooth action,
lifts its actual carrier to `Type (max uF uV)` as required by the genericity
theorem, and transports irreducibility, square-integrability and
unitarizability along the actual representation equivalence. Genericity
is transported back to the original action. Published multiplicity one
and `isOfWhittakerType_of_isGeneric` give full standard Whittaker type,
including finite generation and the functional-space equivalence.
This construction is applied separately to each carrier.

The genericity input is the proved theorem in
`Classification.SquareIntegrableGenericityProof`. It uses the analytic
strong-head segment classification, the singleton normalized-induction
isomorphism with the original representation, and the reverse
generic-product theorem. In particular it supplies the actual nonzero
functional; the final theorem assumes no genericity premise.

Apply `symmetricLPolynomialExists.{uF,uV,uW}` to the two original actions,
the two Whittaker-type proofs and the supplied self-dual measure. This
chooses one polynomial satisfying the full symmetric relation. That
relation includes quotient-measure existence and the normalized-generator
property for every compatible quotient measure.

For this same polynomial, apply
`IsPadicSymmetricLPolynomial.eval_ne_zero_of_squareIntegrable` to the four
original irreducibility and square-integrability hypotheses and any point
of norm less than one. Pairing this conclusion with the polynomial and its
relation proves the exact target.

## Analytic content and provenance

This module assembles published proofs. The sharp analytic estimate and
its denominator consequence are implemented in the imported nonvanishing
proof and its dependencies. For equal ranks,
`squareIntegrableEqualRankAnalytic` gives holomorphy on `Re(s) > 0`
for the intrinsic coefficient-model functions. For unequal ranks,
`squareIntegrableZeroRowAnalytic` gives the needed estimate for the
zero-row block, whose normalized generator is the common denominator.
`holomorphicRationalContinuation` turns that holomorphy into regularity of
each rational zeta value at every nonzero point of the open unit disk.
`IsNormalizedGenerator.eval_ne_zero_of_regularAt` excludes a zero of the
normalized denominator there. Its constant coefficient one handles zero.
The symmetric helper applies the appropriate rank order and swaps both
representations and their hypotheses together.

All analytic square-integrability and compatible quotient-measure
quantifiers remain in the imported predicates. The existence proof
obtains the general analytic generators from the published equal- and
unequal-rank theorems, with character transport and the proved uniqueness
of compatible quotient measures. No pending statement or conditional
comparison is used as a substitute for these proofs.

The original pole-freeness assertion is Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg convolutions*, American Journal of Mathematics
105 (1983), statement (6) of Section 8.2, printed p.445; its analytic proof
is Section 8.3, printed pp.448–451. The registered source is
`jpss-1983-rankin-selberg`; those passages were read directly during this
task. The target's source interpretation and the imported proofs'
individual provenance are preserved. This final assembly adds no separate
classification, analytic convergence or representation-equivalence claim.
