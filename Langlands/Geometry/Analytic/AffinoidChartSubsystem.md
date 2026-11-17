# Open subsystems of affinoid chart gluings

This is an internal construction for the local topology of analytic pullbacks.
It concerns the existing `AffinoidChartSystem` gluing quotient and uses its
original algebras, bounded restrictions, and spectrum maps. It does not assert
existence of a pullback or automatically supply its geometric hypotheses.

A family `S` is `IsDownwardClosed` when every subdomain of a selected chart is
selected. `subsystem S hS` is its chart system. Its meet axiom follows from the
original meet axiom and downward closure. The natural `subsystemMap` to the full
quotient is continuous and injective: any common subdomain witnessing equality
in the full quotient already belongs to the selected family. Its image is
`subsystemSupport S`, the union of the selected original chart images.

For each original chart `j`, `relativePullFamily S j` consists of the images of
all bounded subdomain inclusions from selected charts into `j`, with codomain
restricted to the actual preimage of the support. Each inclusion is an embedding
by the affinoid-domain spectrum embedding theorem. `HasLocalSubchartCover S`
asks that this family be a quasinet: each point has a finite neighborhood union
of these images, all containing that point.

The main theorem `isOpenEmbedding_subsystemMap` assumes that the support has open
preimage in each original chart and that `HasLocalSubchartCover S` holds. It
proves that the subsystem quotient is an open subspace of the full quotient.
To prove openness of the natural map, the proof pulls an image of an open set
back to each original chart, then to the support preimage. The quasinet criterion
tests openness on contained subchart images. On each such image the test agrees
with the original open set pulled back along a subsystem chart. Finally the
open inclusion of the support preimage and the quotient topology give openness
in the full gluing. Continuity and injectivity finish the open-embedding proof.

No ambient Hausdorffness, compactness of the full gluing, equal-universe
assumption, or finite-overlap axiom is used. The field universe `u` and chart-index
universe `w` remain independent; both quotients have their original size
`Type (max u w)`. This module alone does not lower the quotient's universe.
