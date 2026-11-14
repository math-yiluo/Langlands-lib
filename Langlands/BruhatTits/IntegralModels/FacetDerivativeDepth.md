# Facet derivative roots and the doubled-root depth criterion

This internal comparison uses the existing actual affine roots and root
filtrations of `ValuationBuildingData G`, at arbitrary universe `u`.
`facetDepthRoots B x` is the set of actual relative characters `a` for which
`U_{a,x,0}` is not contained in `U_{a,x,0+} · U_{2a}(K)`. The full doubled-root
group is the existing `doubleRootGroupPoints B.i a`, with its existing convention
of the trivial group when `2a` is not a root. The product is a product of sets
of actual rational points of `G`.

`affineFunctional_mem_affineRoots_iff_depth` proves, at every real depth `r`,
that the affine functional with derivative `a` and value `r` at `x` is an
ordinary affine root exactly when `U_{a,x,r}` is not contained in
`U_{a,x,r+} · U_{2a}(K)`. The proof changes from point/depth indexing to affine
root-group indexing using the existing identities for both filtration depths.
In the existential ordinary affine-root definition, the root label is forced
to be the supplied `a` by `rootForm_injective_of_split`, since `B.S` is split.
The converse supplies that root label directly.

`mem_facetDerivativeRoots_facet_iff_affineFunctional` identifies the existing
derivative-root predicate on the full facet of `x` with ordinary affine-root
membership of this normalized functional at depth zero. An affine root
vanishing on the facet vanishes at `x`. Its derivative and value at `x`
determine the functional uniquely, by `AffineMap.ext_linear`. Conversely,
an ordinary affine root vanishing at `x` vanishes everywhere on its full
facet, by `facet_subset_hyperplane`.

Composing these two equivalences gives
`mem_facetDerivativeRoots_facet_iff_depth` for every actual relative root.
`facetDerivativeRoots_eq_facetDepthRoots` expresses the same result as an
equality of sets in the original character lattice. No affine-root-system
axiom or apartment-descent hypothesis is added. Multipliable roots retain the
full doubled-root factor throughout.

The provenance is the internal derivation from these existing Library
definitions and lemmas. This module supplies the geometric depth criterion;
identifying surviving depth classes with roots of an actual special-fibre
quotient, identifying actual model images, and the parabolic order bijection
remain separate obligations.
