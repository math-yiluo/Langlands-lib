# The marked vertex and spin model in local rank-one type D

This internal unit derives a local consequence of the published classical
type-D spin presentation and index comparison. It concerns every nonarchimedean
local field, including characteristic two, and a simply connected absolutely
almost-simple group with an actual type-`D_n` Cartan numbering, `n ≥ 4`.
The full absolute Galois star action is assumed to fix every nonfork vertex,
meaning every vertex with zero-based number `i` satisfying `i + 2 < n`.

`LocalRankOneTypeDPresentation K G n` stores a central division algebra of
dimension four over `K`, a first-kind involution with three-dimensional symmetric
subspace, a nondegenerate Tits quadratic form in `n` variables of quadratic Witt
index one, and an actual morphism from `G` to its isometry group satisfying the
published `IsSpinCover` predicate. The form retains its quotient-valued meaning
in every characteristic.

`localRankOneTypeD_presentation_and_marking` constructs this presentation when
`G` has split rank one. It also proves that the supplied numbering preserves
every Cartan entry and that an actual vertex is distinguished exactly when its
zero-based number is `1`, the vertex numbered 2 in one-based notation.
`localRankOneTypeDPresentation` chooses the established presentation.

The proof applies `classicalTypeDSpinPresentation` to obtain division degree
`degree`, form dimension `m`, and `m * degree = 2 * n`. The local first-kind
involution result `UnitaryInvolution.reducedDegree_dvd_two` implies that the
degree is one or two. Degree one would give a nondegenerate quadratic form of
Witt index one in `2 * n ≥ 8` variables over an algebra of ground-field dimension
one. The bundled scalar quadratic lemma bounds that dimension by six, a
contradiction. Thus `degree = 2`, `m = n`, the division algebra has dimension
four, and the involution's symmetric subspace has dimension three.

The published nonfork marking comparison now makes the vertex numbered 2
distinguished. This vertex is nonfork for `n ≥ 4`, so the assumed full star
action fixes it. At split rank one all distinguished vertices belong to one
orbit of the full absolute Galois group. Every distinguished vertex is therefore
this vertex, which proves the entire marked set, including that the fork tips
are unmarked.

This unit does not assert an upper bound on `n`, determine the star action on
the fork tips, or handle trialitarian numberings without the nonfork-fixing
hypothesis. Those remain separate obligations for the local index enumeration.
