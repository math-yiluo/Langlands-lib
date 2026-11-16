# Smooth normal intersections with parabolics

This internal support result proves smoothness of the scheme-theoretic intersection of a smooth affine normal closed subgroup with a relative parabolic in a reductive group scheme over an arbitrary base.

For a closed subgroup normalized by a cocharacter, equivariance of its induced conjugation action identifies its action parabolic with the inverse image of the ambient dynamic parabolic. The actual intersection's first projection represents precisely this inverse image on every test scheme. The projection is closed because the ambient dynamic representative is closed; its source is therefore affine over the base. The arbitrary-base action-parabolic smoothness theorem applies to this representative.

`normalizedParabolicIntersectionModel` bundles that actual intersection group,
its first projection, its representation of the normalized action parabolic,
and closedness of the projection. Its inputs include the two closed subgroup
inclusions, the dynamic representation of the second inclusion and normalization
of the first subgroup by the cocharacter. The smoothness argument uses this
model's representation field. The model itself needs no smoothness or reductivity
hypothesis.

For a general relative parabolic, `relativeParabolicEtaleLocalDynamic` supplies an étale covering family where its actual inclusion represents a dynamic parabolic. Normality persists under base change and implies normalization by every local cocharacter. The previous argument proves smoothness of each local intersection. The canonical base-change/intersection isomorphism transfers that smoothness to the base changes of the global intersection. Finally `smooth_of_etaleCover` descends smoothness.

The theorem assumes a smooth affine closed normal subgroup and a reductive ambient group. It does not assume that the normal subgroup is reductive, that a central product isogeny is supplied, or that the base is noetherian. It proves smoothness, without asserting parabolicity of the intersection. All constructions and descent inputs come from the published actual subgroup, action, and relative parabolic interfaces; the result is a derived support lemma for the host correspondence.
