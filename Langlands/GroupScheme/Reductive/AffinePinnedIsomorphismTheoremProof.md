# The pinned Isomorphism Theorem over an affine base

Worker 243, with Worker 163 supplying affine pinned uniqueness.

`Langlands.GroupScheme.affinePinnedIsomorphismTheorem` proves exactly
`AffinePinnedIsomorphismTheoremStatement.{u}`, for every universe `u`, with no
additional hypotheses. In particular, the commutative base ring can be zero,
nonreduced, non-Noetherian or disconnected.

The proof applies `affinePinnedIsomorphismTheorem_of_unpinned` to
`affineSplitIsomorphismTheorem`. The latter supplies an actual group-scheme
isomorphism compatible with the prescribed coordinate tori and with the given
root-datum equivalence on characters over every test scheme.

The imported pinned reduction transports each simple-root weight line through
this isomorphism and compares its pinning generator with the target generator
by a unit. It composes with the target scaling automorphism for the inverse
units, which fixes the target torus and corrects the actual differential on
every pinning vector. Its uniqueness proof compares any two isomorphisms
satisfying the full target predicate, using affine pinned rigidity.

This is an internal composite proof. The construction and rigidity arguments
are documented in the imported modules. It changes neither the published target
nor its imports.
