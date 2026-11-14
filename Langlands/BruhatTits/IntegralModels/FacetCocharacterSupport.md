# Actual integral root supports detect incident facet order

This internal module expresses the geometric derivative-facet comparison in
actual characters of the supplied maximal split torus. It retains an arbitrary
field universe `u` and the original affine-root face relation.

For an original incident full facet `F`, `incidentFacetRootSupport B F` is the
set of actual characters belonging to the existing predicate
`facetDerivativeRoots B (facet B.affineRoots x)` whose integer pairing with
`incidentFacetCocharacter B F` is nonnegative. The cocharacter was constructed
in `FacetDerivativeLocalization`; its projected vector lies in the whole
derivative facet of `F`.

`mem_incidentFacetRootSupport_iff` identifies this set, for each actual relative
root, with membership of its actual `rootForm` in the nonnegative linear-root
support of that derivative facet. A functional has constant sign on a full
facet, so testing nonnegativity at the projected cocharacter is equivalent to
testing it at all points. The evaluation identities `rootForm_mk` and
`eval_tmul`, followed by the integer-to-real order comparison, turn that test
into the actual integer lattice pairing. The existing facet-root/derivative
membership equivalence supplies exactly the root-membership condition.

`incidentFacetRootSupport_subset_iff` transfers inclusion between these actual
character sets and the full sets of nonnegative derivative forms. Every
derivative form is a root form of an actual facet derivative character, and
every character in the support is an actual relative root. These coverage
facts suffice; no injectivity assumption on a newly chosen identification is
introduced.

If the actual affine-root set is stable under functional negation,
`isFaceOf_iff_incidentFacetRootSupport_subset` states that `F` is a face of `H`
if and only if the support of `H` is contained in that of `F`.
`incidentFacetRootSupportOrderEmbedding` packages this as an embedding of the
original incident facet face relation into reverse inclusion of character
sets. Its injectivity follows from the same criterion and antisymmetry of the
original face relation. Corrected affine-root-system axioms, including rank
zero, can supply the explicit negation-stability premise.

The provenance is internal: these are direct comparisons of the existing
actual facet-root predicate, integral pairing, derivative support and original
face relation. No finite-segment separation hypothesis is needed here. This
module does not classify parabolic subgroup functors, compare special-fibre
model images or assert a cocharacter ray in the original affine facet; those
are separate obligations of the parabolic-order proof.
