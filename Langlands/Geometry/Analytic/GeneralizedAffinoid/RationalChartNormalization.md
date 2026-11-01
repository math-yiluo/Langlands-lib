# Normalizing rational inequalities after a change of coefficient field

Author: Worker 146.

This internal construction supplies the strict rational input and exact
locus comparison used in scalar descent. Let `d` be an actual
positive-radius rational chart over `A`, let `Q` be a presented strict
affinoid algebra over a complete or incomplete ultrametric field `L`, and
let `ψ : BoundedRingHom A Q`. For each chart coordinate choose `τ j : L`
with norm `d.radii j`.

`d.normalizedStrict Q ψ τ hτ` is actual
`StrictTestDomain.RationalData L Q`. Its denominator is the image of the
original denominator class, and its numerator at `j` is
`algebraMap L Q (τ j)⁻¹ * ψ (presentationMap K A (d.numerators j))`.
The relative radii of this strict rational data are one by construction
of `RationalData`. The coefficient fields and chart index type may have
independent universes.

To verify the absence of common spectrum zeros, the implementation pulls a
spectrum point of `Q` back along `ψ`. A seminorm takes each scalar from
`L` to its prescribed norm. Since every original radius is positive, all
normalizing scalars have nonzero seminorm. Common zeros of the normalized
denominator and numerators would therefore annihilate all original
generators. Their ideal is the unit ideal, contradicting the properness of
the spectrum point's kernel.

`mem_normalizedStrict_locus_iff` proves that the normalized strict locus is
exactly the inverse image of the original locus under
`BanachSpectrum.comap ψ`. It evaluates the inverse scalar norm and
multiplies the inequality by the positive original radius.
`normalizedStrict_locus` states the same result as a set equality.
`normalizedStrict_cover` transfers a covering family along this inverse
image. No surjectivity, finiteness, nonempty cover, or nonzero algebra
assumption is used in this comparison.

The provenance is internal: these are direct consequences of the published
actual quotient-class unit generation, scalar seminorm evaluation, and
rational-locus definitions. The module constructs input data and proves
the locus comparison. Rational quotient transport and scalar section
descent require additional maps and arguments.
