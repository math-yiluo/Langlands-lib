# Reversing segment test tensors in Jacquet multiplicities

Author: Worker 699, adapting the tensor-reindexing calculation in Worker 495's
published `SegmentTensorReversalProof`, with the application coordinated
with Worker 502. This is an internal construction and multiplicity transport.

For every prime, actual p-adic field with supplied compatible topology,
positive block rank, natural factor count, and actual smooth representation
`A`, `segmentTensorReverseEquiv` reindexes the increasing external tensor
along reversal of the uniform Levi coordinates. Its target is the actual
decreasing external tensor. `segmentTensorDownReverseEquiv` constructs the
corresponding equivalence from the pulled-back decreasing tensor to the
increasing tensor. Both include zero factors and require neither
irreducibility nor admissibility of `A`.

`segment_upper_opposite_multiplicity_iff` concerns any actual complex
representation `P` of the ambient general linear group. The field,
factor-carrier and ambient-carrier universes are independent. For every
natural count, the increasing tensor has that count in the upper Jacquet
module of `P` if and only if the decreasing tensor has that count in its
opposite normalized Jacquet module. The second theorem,
`segment_opposite_upper_multiplicity_iff`, compares the increasing tensor's
opposite count with the decreasing tensor's upper count. Each predicate
retains actual finite composition-series witnesses. No finite-length,
smoothness, admissibility or induction assumption is imposed on `P`.

The implementation pulls both ambient and test representations back along
the actual block-label reversal equivalence. The uniform block shape equals
its reverse. The published `oppositeJacquetReverseEquiv` identifies the
pulled-back upper Jacquet module with the actual opposite quotient, with
inverse upper full modulus. The constructed tensor equivalence identifies
the pulled-back test with the decreasing tensor. The published group and
representation multiplicity transport theorems preserve the counts in
both directions. Upper induction, when subsequently used, retains the
existing positive half-modulus covariance and right translation.

The tensor calculations use `FiniteTensor.reindexEquiv Fin.revPerm`.
First they identify the inverse coordinate reindexing in that construction
with `leviReverseEquiv` of the uniform block shape. On each pure tensor,
the increasing calculation uses `i.rev.val = m - 1 - i.val`; the
decreasing calculation uses `m - 1 - i.rev.val = i.val`, where `i.val < m`.
The resulting identity linear equivalences match the reindexed factors to
the factors already defined in `Segments`. The ambient Jacquet comparison
uses the existing block-reversal matrix and its quotient action.

This is internal derived content, rather than a translation of an additional
literature theorem. Its direct imports are `Segments`,
`OppositeCuspidalJacquetFiltrationProof` and `MultiplicityTransportProof`.
The tensor-reindexing and exponent calculation adapts the published segment
tensor reversal argument; the actual quotient comparison and the
witness-preserving multiplicity transports are reused by their Lean names.
Although the opposite-filtration module also contains a conditional
filtration theorem, the auxiliary `oppositeJacquetReverseEquiv` used here is
unconditional. No associated-filtration hypothesis is introduced or
discharged in this module.

The recursive project import audit contains 109 modules including this one.
Its classification modules are exactly `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`,
`OppositeCuspidalJacquetFiltrationStatement`,
`OppositeCuspidalJacquetFiltrationProof`, `Segments`, `Supercuspidal`,
`SupercuspidalTwist` and this module. The remaining imports implement
matrix and block geometry, tensor products, Jacquet quotients, induction
constructions and finite-filtration algebra. No segment constituent
existence, analytic segment classification, socle or special-head
multisegment exhaustion, ordered special-head existence, quotient coverage,
tempered block uniqueness, square-integrable classification or exhaustion,
or regular exhaustion conclusion is used. All 108 imported project Lean
files agree with the supplied published Library tree.

This module supplies no nonzero induction, adjunction, ambient count,
strong head or strong socle. The multiplicity equivalences do not assert
that either finite-series count exists; they transport any count that
exists, including zero, in both directions.
