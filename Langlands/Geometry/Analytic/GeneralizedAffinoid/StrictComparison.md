# Radius-one comparison of actual quotient presentations

Author: Worker 56.

This construction sends a chosen strict affinoid presentation to the
positive-polyradius presentation whose radii are all one and whose ideal is
the inverse image of the original closed ideal under the existing
coefficient-preserving radius-one algebra isometry. Its ideal is closed
because this isometry is continuous.

The induced algebra equivalence between the actual quotient carriers sends
the class of a weighted series to the class of the same strict series. Its
inverse keeps coefficients as well. The two presentation-map equations
are proved directly from the quotient construction.

The comparison preserves the actual quotient norm. In each direction,
representatives map isometrically before passing to the quotient, so the
representatives with arbitrarily small norm excess prove a contraction. The inverse equations
then give equality of norms. The resulting `strictEquiv` is an actual
bounded algebra equivalence with bound one in both directions.
`strictSpectrumHomeomorph` is its concrete contravariant homeomorphism of
bounded multiplicative spectra.

These constructions require an ultrametric normed field but do not require
its completeness or nontrivial valuation. They permit zero variables and
the unit ideal. They compare these two chosen quotient presentation models;
they do not prove that arbitrary positive radii admit strict presentations,
independence of all presentations, or an analytic-space atlas.

This is a derived implementation of the radius-one clause of Berkovich,
*Non-Archimedean analytic spaces* (Trieste lectures, 2009), Definition 2.1.2,
printed/PDF page 7, using the restricted-series norm of Example 1.2.2(v),
page 4, and the quotient norm in the paragraph before Definition 2.1.1,
page 7. The spectrum construction uses Definitions 1.2.3 and 1.2.5 on
page 4. These pages were read directly for this comparison. The source
works over complete fields; this implementation only claims the normed
comparison over incomplete fields. It imports the existing weighted
radius-one isometry, near-minimal quotient representatives and bounded equivalence
spectrum construction by their Lean names.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
