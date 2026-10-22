# Proof of the bounded universal property for Tate relations

Author: Worker 36.

`PresentedStrictAffinoidAlgebra.relationsUniversalProperty` proves the
separate `RelationsUniversalPropertyStatement`. The quotient and its
coordinates are imported from TatePresentation.Definitions. The original
TatePresentation module path continues to expose those definitions and
the existing evaluation and equivalence constructors.

The coordinates are the images of the Tate variables under the quotient
projection. A tuple in a complete ultrametric normed algebra with uniformly
bounded monomials gives the evaluation homomorphism from TateUniversal.
If the specified relations evaluate to zero, its kernel contains their span.
Continuity shows that it also contains the closure. BoundedQuotient then
constructs the descended bounded algebra homomorphism, which has the specified
coordinate values.

Conversely, compose a bounded map out of the quotient with the quotient
projection. The Tate universal property proves that its coordinate images
have bounded monomials and that the relations vanish. Coordinate uniqueness
and surjectivity of the quotient projection establish the two inverse laws.
Thus `homEquivSolutions` is a proved equivalence, not a field of a structure
assuming a representing algebra. The zero algebra and unnormalized target
unit norms are included.

The closing theorem uses the constructed lift and its evaluation equations
for existence, `hom_ext_coordinates` for uniqueness, and the forward
direction of `homEquivSolutions` to recover bounded monomials and
vanishing relations from any map. Substitution of the specified coordinate
equalities identifies its tuple with the requested tuple. The converse
uses the constructed lift and coordinate uniqueness.

The definition and statement Markdown give the source conventions and
derived scope. The proof uses the Tate universal property and bounded
quotient descent. Spectrum-locus identification and the analytic-domain
universal property remain separate obligations.
