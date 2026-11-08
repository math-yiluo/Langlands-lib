# From centered segment rigidity to actual supercuspidal products

This internal adapter converts the numerical conclusion of
`CenteredSegmentFamilyGamma` into an equivalence of actual representations.
It does not prove the global `AssociatedSupercuspidalInductionStatement`.

`Classification.IsUnitarySupercuspidalProduct F T B ρ` means that the supplied
action `ρ` is intertwining-equivalent to the entire normalized upper parabolic
induction, of the specified block shape `B`, of irreducible unitarizable
supercuspidal smooth representations. The output block carriers live in an
independently prescribed universe. The field, source carrier and output block
carrier universes are independent. The predicate retains the supplied topology
and original source action.

`SquareIntegrableSegmentParameter.supercuspidal_of_length_one` applies the
published one-term segment-quotient theorem to the strong head in the supplied
parameter. Equality elimination along the stored degree equality gives
irreducibility and supercuspidality of the original supplied block, on its
original carrier and action.

`unitarySupercuspidalProduct_of_length_one_zero_exponents` assumes chosen segment
parameters with one-term segments, unitarizability of each supplied block, zero
exponents, and an actual intertwining equivalence from the source action to the
whole twisted product. It packages those same original blocks as supercuspidal
representations, composes the supplied equivalence with the published zero-twist
isomorphism of whole normalized products, and applies the published small
supercuspidal-product realization theorem. The shape is preserved, and no
constituent relation replaces the equivalence to the full induction.

`centeredSegmentFamily_unitarySupercuspidalProduct_of_unitaryGenericDatum`
first invokes the proved gamma-germ rigidity adapter for a supplied unitary
generic datum and its chosen square-integrable segment parameters. It then
uses the structural theorem just described. Its premises retain the equal-rank
supercuspidal L-factor statement, the two centered L-product identities for
the actual chosen base Euler factors, the exact rational gamma formula, a
nonzero dual polynomial, the positive-order restriction on the real axis,
and the equivalence to the whole twisted product. The finite block family is
assumed nonempty. The conclusion is an actual unitary supercuspidal product
with an independently prescribed output block universe.

The provenance is composition of the existing
`SupercuspidalInductionTransports`, `SupercuspidalProductRealization`,
`CenteredUnitarySegmentParametrization`, and `CenteredSegmentFamilyGamma`
interfaces. No new assertion from the literature is introduced. In particular,
this module does not discharge classification exhaustion, factor formulas or
global arithmetic witness obligations.
