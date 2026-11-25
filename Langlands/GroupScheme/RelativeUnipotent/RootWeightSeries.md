# Finite vector-bundle series from nonnegative root weights

This internal derived module assembles a finite series
for the represented positive-weight subgroup from a supplied `RootHeightChart`
and independent `RootWeightData` over an arbitrary commutative ring and at
arbitrary universe. The series is on `W.groupScheme 0`, whose ambient weights
are at least one. It is not identified with the ambient chart group: ambient
roots of weight zero can remain outside this positive subgroup.

Term `d` has cutoff `d + 1`. A term whose cutoff exceeds every weight has the
bottom ambient subgroup. Its represented point equivalence is injective, so
every point of this term is the identity, on every scheme test. This proves
`range_id_eq_bot`.

`hasVectorBundleSeries_of_bound` applies the existing finite-segment theorem
to the represented terms starting at index zero. Each successor inclusion is
closed, has smooth source, and has normal pointwise range. Its exact-weight
quotient is a represented fppf quotient with precisely this range as kernel,
by `RootWeightKernel`. Each target is the standard vector group of the exact
support's cardinality; `isVectorBundleAdditive_vectorGroup` identifies its
points naturally on all tests with the sections of an actual finite free
module sheaf. The terminal triviality statement closes the finite recursion.

`weightBound` is the maximum of the finitely many natural weights, with value
zero for an empty family. This yields `hasFiniteVectorBundleSeries` and a chosen
`seriesWitness` of that length. If all weights are zero, the positive subgroup
is trivial and the resulting series has length zero. Empty layers are allowed.

The provenance is the preceding represented positive-weight construction and
the Library's finite-segment and free-vector-bundle theorems. Construction from
every supplied relative parabolic and radical, comparison of these local terms,
and descent remain obligations of the full theorem. No additional literature
translation is claimed.
