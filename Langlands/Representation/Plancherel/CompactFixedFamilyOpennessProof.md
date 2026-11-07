# Compact-fixed family openness

The theorem `Langlands.Plancherel.compactFixedFamilyOpenness` proves the
published `CompactFixedFamilyOpennessStatement`, with independent universes
for the parameter space, group, representation carriers and finite basis
index. It uses the actual normalized compact-fixed projection and compressed
matrices of `UnitarizabilityContinuation`, and allows the representation
carriers to vary with the parameter.

First, `fixedProjection_mem` proves that the normalized projection preserves
each actual invariant submodule. Apply projection naturality to the inclusion
of the corresponding bundled smooth subrepresentation; the projection in
that subrepresentation already takes values in its underlying submodule.

The main pointwise lemma `isIrreducible_of_fixedMatrix` assumes a nonzero
representation and detection of every irreducible actual subquotient by the
given compact open subgroup. The published detection consequences then give
both a nonzero fixed vector in every nonzero subquotient and generation by
fixed vectors.

For a subrepresentation `S`, pull its underlying submodule back through the
chosen coordinate equivalence of the fixed-vector space. The resulting
coordinate subspace is invariant under every compressed matrix: the group
action preserves `S`, and so does the normalized projection. Matrix
irreducibility makes this subspace zero or the whole coordinate space.
In the zero case, if `S` were nonzero, detection applied to its actual bundled
subrepresentation would give a nonzero fixed vector and hence nonzero
coordinates, a contradiction. In the whole-space case, `S` contains every
fixed vector of the original representation, so generation forces `S` to
be the whole representation. The assumed nonzero carrier supplies the
nontriviality part of actual irreducibility.

The existing theorem `fixedMatrix_isIrreducible` gives the reverse
implication, yielding `isIrreducible_iff_fixedMatrix`. Apply this equivalence
at each parameter. The published `finiteMatrixIrreducibilityOpenness`,
using the supplied entrywise continuity, makes the matrix irreducibility
locus open; the equivalence identifies it with the actual irreducibility
locus.

This is an internal derived proof using the published projection,
detection and finite-matrix results. It proves openness under exactly the
auxiliary statement's premises. Applying it to actual unramified parabolic
induction still requires a common detecting compact open subgroup, fixed-space
bases with continuous compressed matrices, nonzero carriers and an
irreducible parameter. This auxiliary proves no nonemptiness assertion and
does not complete `ConditionalParabolicGenericIrreducibilityStatement`.
