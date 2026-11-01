# Signed assembly of whole-target common coefficients

This internal construction assembles the actual whole-target comparison from
`CorrectedWholeTargetEvaluation` into the signed cut-diagram framework. It
uses the genuine bundled support quotients and cut maps from
`BundledJacquetQuotientDiagram`. The hypotheses in `WholeTargetIntervalData`
are explicit construction data to be supplied by the geometric interval and
vanishing arguments: they are not established here or added to the final
signed-effectivity target.

First, a general interval comparison extends supplied linear equivalences on
active coordinates to an equivalence on every coordinate. Outside the
interval the source must be a zero module; the interval model is also zero
there. On active source and target coordinates the supplied square is used.
If the source is inactive, its vanishing forces both images to zero; if the
target is inactive, there is no coordinate value to compare. This gives a
natural equivalence of the entire inclusion diagrams, including maps crossing
the interval boundary.

For the actual geometric assembly, each active cut has its corrected support
membership, source-increasing permutation, actual intersection refinement,
equality of that refinement's flattening with a fixed block shape `Q`, and
whole-target intersection equality. The coordinate comparison is exactly
`Support.correctedWholeTargetCommonEquiv`: coherent normalized orbit
integration, evaluation at the identity of whole-target compact induction,
and the actual common flattened Jacquet quotient comparison. Its proved
all-class cut-map square makes every active transition the identity on that
same actual coefficient `Q.JacquetModule A.representation`.

Applying the general interval comparison gives
`wholeTargetIntervalEquivalence`. Its homogeneous products and differential
square use the generic signed-diagram equivalence, so every original exterior
coefficient `sign s i` is preserved. No equality of unspecified group actions
on the common coefficient is claimed. The supplied topology, arbitrary rank,
and independent universes are retained. The construction does not yet provide
`WholeTargetIntervalData`, prove geometric vanishing or interval exactness, or
prove signed effectivity.
