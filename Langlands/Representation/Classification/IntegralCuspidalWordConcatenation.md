# Concatenating actual integral cuspidal Jacquet words

Authors: Worker 320 (shared Lean proof and initial explanation), Worker 438
(verification, dependency audit and expanded explanation).

This internal adapter starts with an actual external tensor of coarse
representations occurring as a subquotient of an ambient normalized upper
Jacquet module. Each coarse factor has a supplied actual integral cuspidal
Jacquet word on the same twist line. The conclusion realizes the concatenation
of those words in an actual normalized upper Jacquet module of the original
ambient representation.

`integralCuspidalJacquetWord_concatenate` retains arbitrary primes, the supplied
field and topology, independent universes `uF,uV`, and actual factor carriers in
`Type (max uF uV)`. The coarse shape `B` and the total rank are arbitrary.

The proof chooses actual inner block shapes `S i`, supercuspidal
representatives `C i j`, integer functions `e i`, rank-indexed twist identities
and actual tensor occurrences from the supplied words `w i`. It flattens the
shapes with `BlockShape.flatten`, retaining the representatives and labels
through the canonical consecutive dependent-fiber numbering
`B.flattenBlockEquiv S`.

The equality `hblocks` identifies the regrouped flattened tensor in each
coarse slot with the original inner external tensor. Equality elimination
gives heterogeneous equality for the rank transports and for equal dependent
indices; `eq_of_heq` and extensionality give equality of the actual factor
families and their external smooth objects. This retains every original
representative despite the dependent rank types. The inherited rank-indexed
twist identity for each flattened slot follows from its selected inner slot.

The Library's actual
`subquotient_flattenedJacquet_of_coarse_factors` theorem reassembles the inner
tensor occurrences using the given actual coarse occurrence. It uses actual
refined tensor quotient maps, Jacquet exactness, quotient transitivity and
the normalized flattened Jacquet comparison. The finite-list equality
`FiniteConcatenation.ofFn_finSigmaFinEquiv` identifies the resulting labels
with the ordered concatenation of the supplied words, by replacing each
`w i` with its chosen `List.ofFn (e i)`. This list lemma is imported from
`SegmentProductConcatenation`; the present construction uses no segment
product datum or segment-socle hypothesis.

The provenance is internal composition of the published normalized Jacquet
refinement, actual tensor subquotient and finite-list constructions. No
irreducibility or finiteness condition is imposed on the ambient or coarse
objects. There is no positive-total-rank, admissibility or analytic assumption.
The result retains the common actual normalized upper functors and all label
multiplicities.
