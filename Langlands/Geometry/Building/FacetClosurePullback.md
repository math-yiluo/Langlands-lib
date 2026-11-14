# Closed facets from affine segments and facet pullback

This internal derived result concerns arbitrary sets of real affine functionals
on arbitrary real affine spaces. It imposes no affine-root-system axioms and no
topology on the spaces.

A point `q` lies in the combinatorial closure of the facet through `p` exactly
when every point `lineMap q p t` with `0 < t ≤ 1` lies in that facet.
The forward implication follows by evaluating each affine functional on the
segment and checking its sign. For the reverse implication the values of each
functional converge to its value at `q` as the real parameter tends to zero
from above. Closed half-line inequalities pass to that limit; a functional
vanishing at `p` also vanishes at `q`, by its value at the midpoint.

An affine map preserves these segments. Consequently, if the preimage of the
facet through `a p` is exactly the facet through `p` for every `p`, the same
preimage equality holds for their combinatorial closures. This is the theorem
`preimage_facetClosure_of_preimage_facet`. Neither injectivity nor surjectivity of
the affine map is required.

The content is derived directly from the published definitions `facet`,
`facetRel`, and `facetClosure` in `AffineRootSystem`; it asserts no new sourced
classification or building theorem. The segment computation generalizes the
one used by `facetClosure_subset_closure_facet` in
`FacetClosureUnionClosedProof`, dropping that theorem's normed-space
hypotheses because only scalar evaluations and scalar limits are needed here.
