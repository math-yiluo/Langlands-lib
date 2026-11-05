# Actual restriction of curve places and compatible exceptional sets

This derived construction supports the common exceptional-set choice in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10, especially the arithmetic model on p.10.
The registered original has SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

All rings and places here are the original objects. The curve branch takes a
finite extension K → L and a compatible constant-field tower k → K → L, with
all three fields in one arbitrary common universe. There is no separability,
perfectness, or finiteness assumption on k and no function-field presentation
assumption. The number-field branch takes the original map of number fields
K → L. It concerns finite places; the archimedean places are not indexed here.

`curvePlaceRestriction` uses the literal inverse image of the upper valuation
subring under K → L. Its proof verifies that this is a curve place. The
restricted integer-valued valuation is nontrivial: if it were trivial, the
upper valuation would be trivial on K, and any element with nontrivial upper
valuation would be transcendental over K, contradicting algebraicity of L/K.
Its value group is a subgroup of the cyclic group of nonzero integer values,
so Mathlib's principal-ideal theorem for discrete valuations applies. The
constant-field condition follows from the original scalar tower.

The valuation-subring and membership lemmas express literal restriction.
`curvePlaceRestriction_eq_iff` identifies its fibers with the existing
`CurvePlacesAbove` condition. Surjectivity uses the published extension of an
actual lower place. Finiteness of fibers uses the published finiteness of the
full upper-place subtype, and gives the cofinite-filter property.

`curvePlaceExceptionalPreimage` is the finite set of *every* upper place
restricting into a specified finite lower set.
`numberFieldExceptionalPreimage` uses the existing ideal restriction
`HeightOneSpectrum.under` and its published finite-fiber theorem for the same
construction in number fields. Both membership lemmas give precisely the
preimage condition. The two union-image lemmas show that adjoining the
restrictions of any finite upper support to the lower exceptional set makes
the full upper preimage contain that support.

These are constructed finite sets and proved intrinsic laws, not an assumed
place-system interface. The module does not construct a scheme model,
identify an integral closure, prove finiteness of an S-integer extension, or
establish the adelic Weil comparison; those remain separate obligations.
