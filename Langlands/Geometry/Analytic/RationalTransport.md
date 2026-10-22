# Changes of base presentation for rational quotients

Author: Worker 36.

`RationalPresentation.transport` proves the separate
`TransportStatement`: unique transport with prescribed base and coordinate
formulas, and bounded equivalence transport compatible with spectrum maps.

This module constructs transport maps between the actual closed-ideal
quotients defined in `RationalPresentation`. Their relation is
`g * Y_j - f_j`, together with the equations of the base algebra. Given
a bounded base map that takes the actual denominator and numerator
elements to those of another presentation, `map` is a bounded map
between the rational quotients. Source and target base presentations
may have different numbers of variables and different relation sets.

The construction evaluates the source's enlarged Tate algebra at the
images of its old coordinates and the target's new coordinates. The
target quotient projection is bounded, so those new coordinates have
uniformly bounded monomials. Their denominator equations hold by the
target's defining relations. The previously proved `liftFromBase`
therefore supplies the map, and the module proves its restrictions to
the base and to every new coordinate.

`hom_ext_base_coordinates` proves that these restrictions determine any
bounded map from the quotient. It uses the old and new blocks of
coordinates and the Tate-series expansion theorem. Thus inverse
bounded base maps give inverse transport maps: the two composites
are the identity on the base and on each new coordinate.
`equiv` packages the constructed bounded algebra equivalence.
`equivOfLifts` specializes this construction to the identity base map
when different Tate series represent the same denominator and numerators.

No unit-ideal hypothesis is needed for these transport constructions.
They describe the quotient algebra even when it does not represent a
rational domain. The rational-domain identification still has the
precise hypotheses and remaining gaps recorded in `RationalSpectrum`.
No spectral inequality is used to infer power boundedness here.

The induced homeomorphism on the actual multiplicative spectra is
proved to commute with the maps to the base spectra in
`spectrum_equiv_over_base`. Consequently the lift-independence statement
includes the actual algebra, its norm topology, and its spectrum map.

Original-source context is Berkovich, *Non-Archimedean analytic spaces*
(Trieste 2009), Definition 2.1.11 on printed page 8 and Exercise 2.2.2(ii)
on printed page 9. The latter defines the rational quotient in terms
of elements of the base algebra, rather than chosen Tate-series lifts.
The explicit transport and inverse proofs here are derived implementation
lemmas, not quotations or an invocation of the full analytic-domain
universal property in Definition 2.2.1. The closing theorem chooses the
constructed map and equivalence. For uniqueness, another map with the same
two formulas agrees on the base and all new coordinates, so
`hom_ext_base_coordinates` gives equality. The Statement Markdown records
the precise scope and registered source.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
