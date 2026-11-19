# Local finiteness from finite compact neighborhoods

This internal reduction is derived from the published finite-fibre separation
and clopen-restriction results. It deduces local analytic finiteness from
finite pullbacks between compact recognized neighborhoods.

The topological lemma restricts a continuous map to a compact Hausdorff source
piece. At an interior point with finite fibre, the published finite-fibre
separation theorem gives a relatively open neighborhood contained in the
interior of that piece. Intersecting an ambient open representative with the
interior makes this an ambient open neighborhood. The subtype closure formula
transfers the relative closure condition back to the ambient space.

For a strong morphism finite over two recognized compact pieces, the
finite-fibre theorem and the topological lemma give source and target open
neighborhoods. For every recognized subset of the target neighborhood, restrict
its recognized inverse image to the clopen part cut out by the chosen source
open set. Its restriction map is finite Banach, and compatibility of the full
recognition pullbacks identifies the new pullback with its composite with the
original finite Banach map. This proves finiteness at points in both interiors.

The chart version uses the actual recognized inverse images from
`RecognizedFinitePullback`. Finite Banach base change, proved in
`GeneralizedAffinoid/FiniteBanachPushout/Proof`, transfers the finite chart map
to every recognized target subset in its range. The preceding argument then
proves finiteness at points in the interiors of both chart ranges.

The argument generalizes the neighborhood shrinking proof in
`FiniteMorphismSmallNeighborhoods` from initially open source pieces to
recognized compact source pieces. Hausdorffness of those pieces supplies
the separation used in the proof.
