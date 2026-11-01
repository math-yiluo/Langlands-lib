# Signed diagrams of actual bundled support quotients

This internal assembly uses `CorrectedJacquetQuotientComparison` and
`CutDiagramEquivalence`. Its coordinate at the cut set `s` is exactly the
existing `Support.cutSupportQuotient T A C (shape s) theta eta`, and its
inclusion map is exactly the underlying linear map of
`Support.cutSupportQuotientMap`. Thus it retains the original normalized
Jacquet descent of the actual cut transition and the corrected support
images invariant under both relevant Weyl subgroups. No coordinate or map is
replaced by an abstract model.

The identity and composition laws follow from those for the existing
coordinate quotient diagram: every bundled quotient vector has a preimage
under `cutCoordinateQuotientEquiv`, and its already proved map square reduces
each law to the coordinate-diagram law. These equivalences then form a
natural `Diagram.Equivalence`.

`bundledSupportQuotientDegreeEquiv` applies that natural equivalence to the
homogeneous products. Its differential square follows from the generic
signed insertion comparison, preserving every coefficient `sign s i`.
Composing with `correctedGradedEquiv` identifies the actual associated grade
of the homogeneous Jacquet support filtration directly with the bundled
quotient diagram, with the same signed differential.

The last results transport injectivity and middle exactness and lift them
through an empty-to-full finite support filtration, using the previously
proved finite filtered lifts. Injectivity and exactness of the bundled
quotient differentials remain explicit hypotheses. This module establishes
neither their geometric orbit identification nor their Boolean exactness,
and does not claim terminal exactness or signed effectivity. It retains
arbitrary ranks, the supplied topology and independent field and carrier
universes; no nonzero-rank assumption is used.
