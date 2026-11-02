# Global finite first-block Laurent identity

This module is a derived integration step for JPSS, *Rankin–Selberg
convolutions* (1983), Section 4.9, printed pages 416–418, and Section
4.10(2), page 419. The proof also uses the coefficientwise integration of
bilateral Laurent series described in Section 4.1, printed page 406. The
actual quotient towers, raw norm estimates and measurable-kernel packaging
are internal derivations from the imported results.

Fix the canonical p-adic field, a two-block shape, natural row counts j and
k, the supplied additive Haar measure, block representations with supplied
inverse-character functionals, an induced section, and a Whittaker test.
`firstBlockLowerGlobalSeries` is the bilateral series whose coefficient at
integer d is the actual lower quotient-kernel integral over determinant
slice d, using the supplied lower quotient measure.

`firstBlockUpperCoefficient_integrable_of_product` assumes genuine
integrability of the upper row average on the actual
radical/small-quotient/remaining-column product, with small determinant
slice d. Fubini makes its product integral in the first two variables
integrable in the remaining column variable Y. Almost everywhere in Y,
Fubini identifies that product integral with the iterated integral defining
the actual upper coefficient. Thus the upper coefficient is integrable
in Y. No conclusion about convergence is drawn solely from equality of
total integrals.

The published `TwoBlockFirstBlockLaurent.integral_laurent_identity_ae` in
[TwoBlockFirstBlockLaurentReflection](TwoBlockFirstBlockLaurentReflection.md)
is the general integration lemma reused here:
for coefficientwise integrable bilateral series families s and v, an
almost-everywhere equality `D • s = E • v` for fixed finite Laurent
polynomials implies the same equality for their coefficientwise integrals.
The proof commutes the finite Laurent coefficient sums with integration
and integrates the almost-everywhere equality coefficient by coefficient.
It requires no support bound or polynomial cancellation.

`firstBlock_global_laurent_identity` applies this lemma twice. It assumes
a large Whittaker-type representation with its supplied coefficient-model
test, smoothness of the first block representation, an inverse Whittaker
function realizing the actual ordinary Jacquet integral, and absolute
integrability of that Jacquet integral. It takes the actual compatible
large and small unipotent quotient measures, upper block quotient measure,
upper mixed and lower mixed quotient measures, and lower block quotient
measure. The large and small unipotent and upper block measures are
sigma-finite. On every lower determinant slice it assumes integrability
of the actual lower kernel and its raw norm profile and almost-everywhere
integrability of the actual product-rectangle fiber.

Its local algebraic input is the finite identity, at every Y and every
large-base representative g, between the actual reflected smaller
coefficient series and the actual upper first-block coefficient series,
with fixed Laurent factors D and E. This is the local identity supplied by
`firstBlock_small_laurent_identity` when its normalized generators and
common functional-equation witnesses are given. The integration theorem
allows arbitrary D and E and does not itself choose those witnesses.

The conclusion is
`D • Zlow = E • Zup`, where Zlow consists of the actual lower slice
integrals and Zup consists of the actual large upper JPSS iterated slice
integrals, at spectral parameter zero. Every supplied measure is retained.
All j and k, including zero, and zero functionals are allowed whenever
the stated hypotheses hold.

For each integer d, `firstBlockReflectedQuotientAverage_analysis` supplies
the integrable lower mixed quotient average and its almost-everywhere
Y integral formula. The upper counterpart supplies integrability of its
quotient average and genuine triple-product convergence. Countability of
the integers gives a common full-measure set on which these formulas hold
for every coefficient. At a fixed quotient point any group representative
can be used; no measurable representative is selected. The preceding
upper coefficient integrability lemma and the reflected convergence
formula justify integrating the local identity in Y. This gives the
finite Laurent identity almost everywhere on the lower mixed zero slice.
Both quotient-average families are coefficientwise integrable, so the
general integration lemma applies there too. The exact lower slice tower
and the exact upper Jacquet unfolding identify their integrals with Zlow
and Zup, respectively.

This result is the conditional analytic and algebraic bridge used to
assemble the closed strictly dominant target. It does not derive a uniform
twist bound, construct a Jacquet functional, or produce the common
normalized-generator witnesses. Those inputs are supplied separately.
