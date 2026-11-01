# Reduction to the isolated uniform local triple input

This internal contribution proves the conditional reduction
`repeatedCuspidalTripleJacquetTransfer_of_uniform`. Its sole extra hypothesis
is `UniformRepeatedCuspidalTripleJacquetTransfer F T`, and its conclusion is
the exact Library proposition `Classification.RepeatedCuspidalTripleJacquetTransfer
F T`. The uniform input remains unproved here, so this reduction does not
complete the ambient proof task.

`ThreeSlotRepeatedCuspidalTransfer` states the same two local moves for an
arbitrary actual block shape of length three. Its class equalities are in the
dependent sum of ranks and supercuspidal classes. In each branch the first
coordinates of these equalities force all three ranks to coincide. The sum of
the block sizes then identifies the total rank with `d + (d + d)`, and
`BlockShape.ext_of_size` identifies the shape with `threeBlocks d d d`.
The proof eliminates these equalities and applies the uniform local input.
Finite case analysis identifies the original and swapped factor families.
The transport helpers eliminate equality of shapes or permutations; they
preserve the actual smooth objects and actual subquotient relation.

For the ambient theorem the proof extracts one family of actual irreducible,
admissible, finite-length coarse factors using `exists_tripleCoarseFactors`.
This extraction keeps the selected three slots together and retains every
outside singleton. `tripleInnerSupercuspidalFamily` takes the supplied
supercuspidal objects at the exact nested block labels; it chooses no new
class representatives. Congruence of the rank-indexed class functions along
the three label identities supplies the local class hypotheses. The
three-slot transfer gives the selected new occurrence. Finally,
`subquotient_tripleSwapJacquet_of_selected` reassembles the globally permuted
tensor using that occurrence and all the original outside occurrences.
The second branch chooses its adjacent swap only after this common coarse
extraction. Every occurrence is an actual `SmoothRep.IsSubquotient` in the
normalized Jacquet module of the same ambient representation.

The field and representation universes remain independent. The ambient
reduction applies the uniform input with representation universe `max uF uV`,
as required by the published target. It retains arbitrary supplied `p`, `F`,
and topological data `T`, unrestricted outside factors, and both implications
of the conjunction. The ambient irreducibility hypothesis is accepted by the
target; the coarse extraction needs only its explicit admissibility and
composition finite length.

The provenance is internal equality transport and composition of the existing
actual extraction and return interfaces. No source claim about the local
representation theory is added. The imported occurrence adapters use actual
image filtrations, exact smooth Jacquet functors, tensor presentations,
explicit refinement comparisons and admissible irreducible factorization.
Their previously audited proofs use compact averaging, Schur and density
arguments, and lower finite-length arguments; they do not use any of the
eight excluded classification conclusions. This module adds only rank,
shape, label and family equalities and applications of those adapters. A
workspace import audit records 407 project modules, all with Markdown
companions. The named local input remains explicit throughout; no
classification assertion is hidden in a new axiom or an unconditional
conclusion. Worker 1216 authored the reused ordered occurrence adapter.
