# Adjacent descents of coordinate permutations

This module supplies an internal finite combinatorial adapter for the actual
permutations and ordered positive block shapes in `Geometric.WeylDefinitions`.
It translates the two order clauses of a minimal representative into tests on
adjacent edges. Its provenance is the concrete definitions and elementary
finite linear order arguments; no assertion from external literature or
representation classification is used.

For `w : Equiv.Perm (Fin n)`, `permutationDescents w` is the finite set of
`i : Fin (n - 1)` such that `w(i+1) < w(i)`. The edge numbered `i` joins
coordinate `i` to coordinate `i+1`, so it uses the same zero-based edge convention
as the block cut sets. `mem_permutationDescents` exposes this definition.

`strictMono_blocks_iff_descents` says that `w` increases strictly inside each
block of `B` if and only if the endpoints of every descent have different
`blockIndex B` labels. In the forward direction, the two endpoints of a
hypothetical same-block descent can be written in the coordinates of their
common block. The published strict monotonicity of the block coordinate
embedding orders those coordinates, contradicting the descent. Conversely,
the proof tests adjacent coordinates inside a block. The explicit consecutive
numbering shows that they are an ambient adjacent pair with equal block
labels. Injectivity of `w` rules out equal images, and a decreasing pair would
contradict the hypothesis. Adjacent increases imply strict monotonicity on a
finite line, using `Fin.strictMono_iff_lt_succ`.

`isMinimalRepresentative_iff_descents` applies this equivalence first to the
source shape `B` and `w`, then to the target shape `C` and `w.symm`.
Thus the argument order and source-to-target convention of
`IsMinimalRepresentative B C w` are retained.

`permutationDescents_one` proves that the identity has no descents.
`permutationDescents_eq_empty_iff` gives the converse: no adjacent descent
implies that the permutation is strictly increasing, and a strictly increasing
endomorphism of a finite linear order is the identity.

All definitions and results quantify over every natural rank. At ranks zero
and one there are no interior edges. Their permutation group is trivial, so
the empty-descent characterization retains these cases. The block arguments
use the existing positive shapes, without adding a positive-rank hypothesis.

This module does not yet identify different adjacent block labels with the
published cut set, nor prove a signed cancellation identity, a geometric lemma,
an Aubert identity or the segment classification.
