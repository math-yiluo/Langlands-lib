# Invariant compact open cutoffs in the full-rank rectangular locus

This internal topological construction supports approximation by compact tests.
The open full-row-rank locus is described by existence of a matrix right inverse.
At a right-invertible matrix M with right inverse R, the condition det(NR) nonzero
is an open neighborhood inside that locus: invertibility of NR gives a right
inverse R(NR) inverse for N. All row counts, including zero, are included.

An open subset of a locally compact, Hausdorff, totally disconnected,
second-countable space has an exhaustion by compact clopen ambient subsets.
The proof chooses compact clopen neighborhoods inside the open set, takes
finite subcovers of a compact covering of the open subtype, then finite
accumulations. Each point is eventually in every later set.

For any compact subgroup J of the rectangular right action, saturation of each
such cutoff by J is compact, open and still full rank. Membership in its
saturation is invariant under right multiplication by J. These saturated
sets eventually contain every full-rank rectangular matrix. No field
valuation, representation, Haar measure or convergence assertion is needed
for these geometric facts.

`adjacentRankCutoffTest` multiplies an arbitrary rectangular Schwartz–Bruhat
function by the value-one indicator of a compact open full-rank set. Its
entire topological support is full rank, so it belongs to the existing
`adjacentRankCompactTests` space. Its values are exactly the original test
inside the cutoff and zero outside; its pointwise norm is consequently bounded
by that of the original test.

`exists_adjacentRankFullRankTestApproximation` combines those restrictions
with the saturated exhaustion. If the original test is invariant under the
right action of the compact subgroup J, every restricted test is invariant
under the same subgroup. At each full-rank matrix, the restrictions eventually
equal the original test. This is a pointwise approximation assertion on the
full-rank locus, with no assertion of convergence at rank-deficient matrices,
no integration assertion, and no equality of test-function spaces.
