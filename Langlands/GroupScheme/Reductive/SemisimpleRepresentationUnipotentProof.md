# Normal unipotent subgroups and semisimple representations

This module proves the unchanged published proposition
`Langlands.GroupScheme.SemisimpleRepresentationUnipotentStatement.{u}` by
`Langlands.GroupScheme.semisimpleRepresentationUnipotent.{u}`. The theorem
has no additional hypotheses and is uniform in the field's universe.

The statement covers affine group schemes locally of finite type over every
field. A normal unipotent closed subgroup acts trivially on every finite
matrix representation whose simple stable subspaces have supremum equal to
the whole coordinate space. If a smooth connected such group has a faithful
semisimple matrix representation, its unipotent radical is trivial. Here
faithful means a closed immersion, and the radical is over the original field,
as in the imported statement.

## Implemented proof

The helper `isStableSubspace_fixedSubmodule_of_normal` applies the published
`normal_fixed_coefficient` theorem using an affine model of the subgroup.
Every linear coefficient of a translate of a fixed vector is again fixed.
Thus the full all-scheme-test fixed submodule is stable in the statement's
all-affine-test sense.

For a simple stable subspace `W`, the helper
`le_fixedSubmodule_of_simple` intersects `W` with that fixed submodule.
The intersection is stable. The published
`IsStableSubspace.exists_nonzero_subgroup_fixedVector` gives a nonzero vector
in the intersection by putting `W` in split finite coordinates and applying
the definition of unipotence to the restricted representation. Simplicity
therefore makes the intersection equal to `W`. Closedness of the subgroup
supplies its affineness; the fixed-vector theorem needs only affineness of
the ambient group.

Every simple stable subspace is consequently contained in the fixed
submodule. Taking their supremum and using semisimplicity shows that all
vectors are fixed. The helper `eq_trivial_of_fixedSubmodule_eq_top` tests the
standard coordinate vectors on every relative scheme: each point matrix is
the identity, hence the representation is the trivial group-scheme morphism.
This argument includes dimension zero without a nonzero-dimensional premise.

For the radical assertion, apply the first assertion to each subgroup in
`HasTrivialUnipotentRadical`. Its composite with the faithful representation
is trivial. The underlying closed immersion is a monomorphism, so cancellation
on every relative scheme test shows that the subgroup's image is the identity.
Its range functor is therefore the bottom subgroup functor. The proof does
not use the smoothness and connectedness assumptions retained by the
published statement.

## Provenance

The route is Milne, *Algebraic Groups* (2017), Lemma 19.16 and Proposition
19.17, printed p.401 (PDF p.417), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original proof passes from nonzero fixed vectors in simple summands to
triviality on their sum, and then cancels a faithful representation. The
Lean proof implements that route with an intersection and the supremum of
simple stable subspaces. The helper lemmas are internal consequences of
the already published coordinate and fixed-vector interfaces.

The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it lists no
correction to Lemma 19.16 or Proposition 19.17. The statement and every pair
it imports are used unchanged.
