# Continuity and surjectivity of algebraic-space point maps

This internal supporting module proves that every algebraic-space morphism
induces a continuous map on its actual point spaces. It also proves that a
representable geometrically surjective transformation of arbitrary
presheaves is surjective on their quotient point sets. There are no
finiteness, quasi-separatedness or representability hypotheses on the
algebraic-space morphism in the continuity assertion.

`Points.continuous_map_of_atlas` is more general: for any transformation
`f : F → G` of presheaves over `S`, a surjective étale scheme chart of the
target `G` suffices for continuity with respect to `pointTopology F` and
`pointTopology G`. Test continuity on an arbitrary étale scheme chart
`h_U → F`. Pull the chosen target atlas back along its composite to `G`.
The represented projection to `U` is étale and surjective, hence its
ordinary point map is a quotient map. The other projection is an actual
scheme map to the target atlas scheme. The chart square commutes on
points, so the composite into the target point space is continuous after
this quotient map, and therefore is continuous before it. The final
topology defining `pointTopology F` gives the claimed continuity of `f`.

For `Points.surjective_map`, represent a target point by a field-valued
section. Pull the given geometrically surjective transformation back to
that represented field test. The resulting scheme projection is
surjective on ordinary points, so the unique point of the field spectrum
lifts. The other represented projection supplies a source presheaf point.
The cartesian square and the residue-field description of the field test
show that this point maps to the original target point. This argument
requires neither presheaf to be a sheaf or to have an atlas.

`Points.continuous_map` chooses a surjective étale chart of the target
algebraic space and applies the general continuity result.
`Points.spaceContinuousMap` bundles the exact induced point function with
that continuity proof.

The provenance is internal: these results follow from represented
pullbacks, the published relative étale and surjectivity predicates,
ordinary scheme continuity, and the existing atlas quotient and point
constructions. No external assertion is assumed. They provide point-map
infrastructure for the connected-fibre argument and do not prove eventual
limit descent or complete `SpaceLimitPropertyDescentStatement`.
