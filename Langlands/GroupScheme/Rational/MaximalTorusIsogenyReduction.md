# Maximal-torus isogeny reduction

Authors: Worker 1371 and Worker 1531.

This module proves exactly `MaximalTorusIsogenyReductionStatement.{u}` from
`Rational/MaximalTorusConjugatorReductionCases`, for an arbitrary universe and
an arbitrary field. The original maximal torus is retained through the
characteristic-dependent semisimple reduction. The proof is an internal
derivation from the published semisimple reduction constructions and the
maximal-torus image, normalizer reflection and nilpotent-normalizer helpers.

The internal `MaximalTorusReductionTarget` extends `SemisimpleReductionTarget`
by recording a chosen maximal torus, normalizer reflection from the original
torus, and local finite presentation of the isogeny. The identity records
the original torus. An outgoing central isogeny records the schematic image
of the current torus, which is maximal and whose restriction is fpqc.
Central-isogeny normalizer reflection composes with the recorded reflection;
local finite presentation composes as well. No centrality of the composite
isogeny is required.

Suppose every recorded target lacks both geometric nilpotence and a
noncentral geometric semisimple tangent. All geometric semisimple tangents
then have full Lie centralizer. In characteristic zero the published
central-torus argument makes the identity target nilpotent. In positive
characteristic the centre-tangent-kernel central isogeny supplies another
recorded target; its geometric pullback kills the tangent image of any
fixed split torus. The published root-division termination theorem applies
to this larger family of targets. Hence a split geometric maximal torus of
the identity target has empty roots and is central, which again implies
geometric nilpotence. Both cases contradict the assumption.

A resulting target supplies its isogeny and chosen maximal torus. The map
is finite, flat and surjective, hence quasi-compact, and its retained local
finite presentation together with flatness gives universal openness. The
published smooth-isogeny dimension theorem gives equality of Lie dimensions
and thus the required inequality. In the nilpotent alternative every point
normalizes the retained torus, by its centrality over the original field.
The other alternative is precisely the published geometric semisimple
predicate. The construction adds no infinitude, perfectness, reductivity,
splitness or characteristic assumption to the exact statement.
