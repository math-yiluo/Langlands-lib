# Elementary tools for quaternionic forms and their Witt indices

Author: Worker 118.

This internal helper module develops the actual definitions in
`Langlands.GroupScheme.Quaternionic.Forms`. It works over any division algebra
with a first-kind involution, for a finite index type, in arbitrary universes.
There is no restriction on characteristic, centrality, or dimension of the algebra.

The sesquilinear identities expand the finite sums in `sesqForm`. Applying the
involution interchanges the vectors and replaces the Gram matrix by its conjugate
transpose. For an antihermitian Gram matrix this gives the antihermitian interchange
law. A line is totally isotropic exactly when its generating vector has zero
self-pairing; the proof writes both vectors as scalar multiples of the generator.

The module proves that every totally isotropic subspace has dimension at most the
Witt index, that the Witt index is bounded by the number of variables, and that a
totally isotropic subspace attains it. The dimensions form a nonempty finite subset
of the natural numbers: the zero subspace supplies zero, and subspace dimension is
bounded by the dimension of the full row space. The maximum assertion uses
`Set.Nonempty.csSup_mem`. As consequences, positivity of the Witt index is equivalent
to the existence of a nonzero isotropic vector, and Witt index one is equivalent
to such existence together with the dimension bound one for every totally
isotropic subspace.

The noncomputable definition `wittSubspace H` chooses a totally isotropic subspace
of dimension `wittIndex H`. Its isotropy and dimension are proved by the maximum
assertion above. The choice is not canonical, and no functoriality is asserted.

These are elementary consequences of the published definitions, provided for the
split-rank comparison in `LocalSymplecticRankOneStatement`. This module establishes
no structural property of a group scheme.
