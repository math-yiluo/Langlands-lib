# Finite covers of compact subsets by quasinet members

This internal topological helper derives finite covering results from the
existing `IsQuasinet` and `IsNet` predicates. The ambient space has an arbitrary
topology. No Hausdorffness, directedness, nonemptiness or compactness of the
individual quasinet members is assumed.

`IsQuasinet.exists_finite_cover_of_isCompact` gives a finite set of members
whose union contains any given compact subset. At every point the quasinet
provides a finite family whose union is a neighborhood. Mathlib's compact
neighborhood subcover theorem selects finitely many such neighborhoods. The
union of their finite families is the required finite family of original
members. Empty compact subsets are included.

`exists_finite_cover_of_restrictedFamily` applies this result in the actual
subspace `Y`. A compact ambient subset contained in `Y` has compact preimage
under the inducing subtype inclusion. Images of the selected subspace members
are exactly the original members contained in `Y`. The theorem retains both
membership in the original family and containment in `Y`.

`IsNet.exists_finite_cover_of_subset_inter` applies that result to the net
axiom on the intersection of any two original members. It gives a finite
cover of every compact subset of their intersection by original members
contained in both.

These are derived helpers for constructing actual finite domain covers in
affinoid atlases. Their provenance is the existing project predicates, the
elementary finite-union argument above, and Mathlib compactness and subspace
topology. They make no new original-literature attribution.
