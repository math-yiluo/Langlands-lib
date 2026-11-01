# Actual Jacquet coefficient series at the equal-rank boundary

Worker 484 assembles the published ordinary Jacquet realization, quotient
integrand and equal-rank support theorem. This is internal derived content.
The module concerns test rank equal to the total induced rank. It does not
prove either final dominant-rank gamma or L comparison.

`unfoldedJacquetSeries` retains the supplied rectangular measure and the
supplied measure on the upper-unipotent quotient. Its integer coefficient is
the restricted Bochner integral of the radical average of the actual first
unfolding integrand, over the corresponding determinant slice.

`lowerInduced_inverseWhittakerType` uses the actual normalized lower-to-upper
reversal equivalence. It reverses the sizes, carriers and representations,
applies the published `normalizedProductWhittakerType`, transports full type
back through the equivalence, then changes the standard character to its
inverse. Reducible full-type blocks are allowed.

`radicalAverage_eq_equalRankIntegrand` assumes an actual inverse-character
functional whose coefficients equal the ordinary Jacquet integrals for all
sections and group elements, and an additive Haar measure on the rectangle.
The representative formula of the published radical average, followed by
the supplied coefficient equation, identifies it with the equal-rank
integrand at zero. The second Whittaker function is the actual coefficient
image `modelMap` of the section. Quotient induction proves equality on the
whole quotient. `unfoldedJacquetSeries_eq` applies the slice integral to this
identity. These two identities concern total Bochner integrals and assert no
convergence themselves.

`unfoldedJacquetSeries_lowerSupport` assumes full standard type of the blocks
and test representation and an arbitrary compatible quotient measure. It
rewrites by the coefficient-series identification and applies the published
`equalRankSliceSupport` with the actual lower induction and the actual
coefficient image. Full inverse type of that induction is the preceding
reversal result. The negative-tail bound may depend on the section,
coefficient and row test. Zero sections, functionals and test coefficients
are allowed in these conditional statements. Independent field, test
carrier and block carrier universes are retained.

`exists_supported_unfoldedJacquetSeries` discharges the ordinary realization
premise in the large-real-parameter range. For full-type blocks `τ` and
supplied nonzero inverse-character block functionals, it applies the published
`twoBlockOrdinaryJacquetFunctional` with the supplied self-dual additive Haar
measure. It keeps that theorem's single real convergence bound `C`. For every
`u > C`, the actual lower induction of the opposite twists has absolutely
integrable raw Jacquet integrands at every group element, and a nonzero
inverse-character functional `J` realizes those integrals as coefficients.
The bound precedes every compatible quotient measure, test representation,
functional, test coefficient, section and row test. The functional `J` also
precedes all these data. Full type transfers to the opposite twists by the
published twist equivalence. Applying the generic series equality and support
lemma then gives both conclusions for every compatible quotient measure and
every full-type test representation. Nonzero block functionals are needed
only in this existence theorem; zero test functionals, test coefficients,
sections and row tests remain included. The canonical field structures are
fixed local instances, so no additional topology, measurability or local-field
hypotheses are generalized into these declarations.

The support bound itself may depend on the section, coefficient and row test;
there is no assertion of one support bound for a parameter family. The final
theorem proves raw Jacquet integrability, but does not assert absolute
integrability of the outer slice integrals or a normalized quotient-tower
identity. Those remain supplied by the separate published fixed-slice
unfolding theorem when needed. No first-block functional equation, lower
Fourier identity, dual-section comparison, spectral uniqueness, rational
continuation or final factor certificate is asserted. In particular the
strict dominant range, test rank greater than induced rank, is not treated
by this equal-rank specialization.
