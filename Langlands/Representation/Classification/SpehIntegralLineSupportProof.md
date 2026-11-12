# Speh cuspidal support on one integral twist line

`Langlands.Classification.spehIntegralLineSupport` proves the exact proposition
`SpehIntegralLineSupport` for independent field and representation universes.

The proof applies the published
`segmentEssentialSquareIntegrableClassification` to the irreducible
square-integrable block `δ` in the supplied Speh datum. This gives a segment
`Δ` and the strong segment-head relation for the original block, after its
rank equality is transported. Real-twist compatibility gives segment heads
for `Δ.twist ((k - 1)/2 - i)` whose actual representations are the blocks of
the centered Speh induction.

`segmentHeadProductCuspidalQuotient` constructs an actual surjection from the
cuspidal members of those segments to that centered induction. Composing it
with the irreducible quotient map in `IsSpeh` supplies the required
`IsSupercuspidalSupport` witness for the given representation `S`.
Multiplicities and actual cuspidal representatives are retained.

Each support member is `Δ.base.twist ((k - 1)/2 - i + j)`. The proof chooses
`ρ = Δ.base.twist ((k - 1)/2)` and the integer `j - i`, then uses the real-twist
addition law and ring arithmetic. It does not use the uniqueness clause of
`IsSpeh`, unitarizability of `S`, or a multisegment exhaustion result.

This is a derived result from the published square-integrable segment
classification, segment-head real-twist compatibility, and cuspidal quotient
construction. It is the single-line support prerequisite for the complementary
Speh irreducibility argument; the separate issue of irreducibility for products
on different lines is not asserted here.
