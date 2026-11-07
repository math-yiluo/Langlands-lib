# Simplicial faces from affinely independent actual facet vertices

This derived construction uses the original sign-defined facets and actual
vertices. It retains the supplied corrected affine root system and finite
dimensional real normed translation space. Affine independence of the indicated
actual vertex family is an explicit additional hypothesis.

`affineMap_eq_zero_on_facetClosure` first works on a general real affine torsor
and a locally finite reflection arrangement. An affine functional nonnegative
on a given original closed facet and zero at a point of it vanishes on that
point's original closed facet. Indeed, extend a short segment from that point
away from any point of its closed facet. Vanishing roots stay zero and local
sign stability preserves all other root signs, so the extension remains in the
original open facet. Nonnegativity of the functional at the extension and at
the other endpoint forces its value at that endpoint to be zero.

`facetClosureVertexFinset_centroid_eq_of_affineIndependent` works on the vector
space itself. If the actual vertices of an original closed facet are affinely
independent, every nonempty subset of them is exactly the actual vertex finset
of its centroid's original facet. No cancellation of root signs gives one
inclusion. To exclude an extra vertex, extend the independent family to an
affine basis and use the extra vertex's affine coordinate. It is nonnegative on
all original vertices and hence on their convex hull, the entire original
closed facet. It vanishes on the chosen subset and its centroid, so the
supporting-functional result makes it vanish at the extra vertex. This
contradicts the coordinate's value one there.

`facetVertexSet Ψ p` is the entire set of vertices of the original closed facet
of `p`, viewed in the original vertex type `{v : V // IsVertex Ψ v}`. This set
is finite and nonempty, including rank zero. Inclusion of these sets is
equivalent to inclusion of the original closed facets. Equality is therefore
also reflected. The existing comparison of original face incidence with
closed-facet containment gives `isFaceOf_facet_iff_facetVertexSet_subset`.

`exists_facetVertexSet_eq_of_nonempty_subset` expresses the centroid result
for subsets of the original vertex type. A subset of one original facet's
vertices is finite. Map its finite set into the ambient vector space and
apply the centroid theorem there. Exact membership of the actual vertex
finsets then shows that the centroid's entire original vertex set is the
chosen subset.

`facetVertexSimplicialComplex` assumes that **every** original facet's entire
actual vertex family is affinely independent. Its vertices are exactly the
original vertices, and its faces are exactly the sets `facetVertexSet Ψ p`,
as `p` ranges over the original vector space. Finiteness and nonemptiness are
the results just described. The subset theorem proves that every nonempty
subset of a face is itself a face; it also supplies every singleton face.
Thus the construction does not enlarge the face collection to arbitrary
subsets without proving that they are original faces.

`closedFacetSimplicialOrderIso` identifies the original closed facets, ordered
by their original containment, with these simplices. The map takes an original
closed facet to its entire actual vertex set. Reflection of containment
proves that it is an order embedding, and the exact definition of the face
collection proves surjectivity. The chosen point representing a closed facet
has no effect on its vertex set, by the equality criterion.

`facetVertexPolysimplicialComplex` packages the same simplicial complex as a
single factor. `closedFacetPolysimplicialOrderIso` uses the constant family
over a singleton index and the existing product-facet order isomorphism to
identify its facets with the original closed facets. Hence
`isPolysimplicial_closedFacets_of_affineIndependent` proves polysimpliciality
of the original closed-facet order under the explicit independence premise.
These maps preserve and reflect the existing original affine face relation;
they introduce no subdivision or replacement incidence.

The result is derived from the existing local sign stability, finite vertex
generation and centroid theorems, with Mathlib's affine basis extension and
coordinate formulas, and the existing abstract simplicial and product
definitions. It introduces no new literature assertion. The supporting
functional theorem retains independent universes for the translation and
point types; the complex construction works on the vector space in arbitrary
universe `u` and retains rank zero.

The file does not assert affine independence for arbitrary affine root
systems: a product facet can have dependent vertices. Proving independence
for actual irreducible factors, constructing those factors and proving their
product decomposition remain separate obligations. The supplied affine root
system is not constructed here. No valued-root datum, original quotient
realization or any of the host task's five unconditional axiom witnesses is
constructed by this conditional criterion.
