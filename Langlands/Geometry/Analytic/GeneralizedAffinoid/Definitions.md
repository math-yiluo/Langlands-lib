# Finite positive-polyradius quotient presentations

Authors: Worker 56 and Worker 36. Worker 56 extends the construction to
arbitrary positive polyradii; the quotient norm, ultrametric proof and
bounded-map category adapt Worker 36's published strict affinoid construction.

`PresentedAffinoidAlgebra K` contains a finite number of variables, one
strictly positive real radius for each variable, and a closed ideal of the
actual weighted restricted-series algebra. Its carrier is the actual ring
quotient by that ideal. Mathlib constructs the quotient norm and normed
algebra; the carrier is not supplied as an unspecified algebra.

The norm is ultrametric. The proof chooses representatives of two quotient
elements with norms within an arbitrary positive epsilon of their quotient
norms, uses the weighted Tate algebra's strong triangle inequality, and then
removes epsilon. The presentation map is an actual surjective algebra map
with norm bound one. Its kernel is precisely the displayed ideal. Every
quotient element has representatives with arbitrarily small positive norm
excess. These properties concern the actual quotient norm.

The coordinate elements are the images of the coefficient-one monomials
with a single exponent one. Their norms are at most their specified radii,
by the exact weighted monomial norm and the contraction of the quotient map.
The zero ideal gives the presented polydisc for every positive polyradius.
The unit ideal and zero variables are permitted.

Morphisms are the existing `BoundedAlgHom` between these quotient algebras;
their identity, composition and category laws are inherited by explicit
construction. `PresentedAffinoidSpace` is the opposite category. Its
topological functor uses the actual bounded multiplicative spectrum of
each quotient normed algebra, with the topology of pointwise evaluation.
On maps it pulls seminorms back along the actual bounded homomorphism.
Functor laws follow pointwise. This construction uses the existing
`BanachSpectrum`, which is defined for normed rings without completeness.

The coefficient field can be incomplete and can have trivial valuation.
Radii need not lie in its value group or its divisible closure.
This file provides the normed quotient and categorical portion of chosen
affinoid presentations. It supplies no `CompleteSpace` instance, Banach
bundle, structure sheaf, atlas or analytic-domain universal property.
Completeness over complete coefficients is a separate obligation that
depends on the weighted Tate completeness proof. In particular, this file
does not assert that its objects over an incomplete field are Banach
affinoid algebras in the source's sense.

The original source is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009): Example 1.2.2(v), page 4, gives the weighted Tate
algebra; the paragraph before Definition 2.1.1, page 7, gives the quotient
norm; Definitions 2.1.1 and 2.1.2, page 7, describe admissible presentations
and affinoid algebras; Definition 2.1.11, page 8, gives the opposite category
with bounded homomorphisms. Definitions 1.2.3 and 1.2.5, page 4, give the
bounded multiplicative spectrum and its topology. These pages were read
directly when preparing this file. Registered original:
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.

This is a derived presentation model: it chooses the closed ideal and the
exact quotient norm instead of starting from an arbitrary admissible
epimorphism onto a Banach algebra. Closedness is a condition on the actual
ideal, not an assumed theorem that every ideal is closed. Noetherianity,
automatic ideal closedness, independence of presentations, comparison with
other equivalent norms and identification of the strict subcategory remain
separate results. The source's completed Banach affinoid construction will
also require the deferred completeness instance.
