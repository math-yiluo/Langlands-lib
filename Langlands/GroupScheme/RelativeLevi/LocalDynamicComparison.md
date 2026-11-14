# Dynamic comparison near a field-valued point

This internal supporting result compares a monic subgroup with a dynamic
parabolic over an arbitrary base scheme. Both ambient and subgroup schemes
are smooth and affine, with geometrically connected fibres. A cocharacter
is given in the subgroup itself. If at a specified field-valued point the
subgroup inclusion is closed and represents the dynamic parabolic of the
composite cocharacter, it does so over an open neighbourhood through which
that field-valued point factors.

`OpenDynamicComparisonStatement` records this assertion;
`openDynamicComparison` proves it, using `exists_open`.

The proof chooses representatives `D` of the subgroup's dynamic parabolic
and `Q` of the ambient dynamic parabolic. Functoriality gives a map `D → Q`
compatible with both inclusions. The closed-subgroup formula at the given
field-valued point makes the dynamic parabolic of the subgroup the whole
subgroup. Thus `D → P` is an isomorphism there, and uniqueness of
representatives makes `D → Q` an isomorphism there as well. Both maps are
monic maps of smooth affine groups with geometrically connected fibres, so
the open isomorphism comparison applies to each. On the intersection of
the resulting opens, their inverses identify `P` with `Q` compatibly with
the original inclusion, proving equality of the subgroup functors on every
test scheme.

All inputs are published Library constructions or the separately reviewed
`SmoothIsomorphismLocus` comparison and its Lie-rank prerequisite. The
provenance is internal. This unit is a supporting step toward relative
parabolic closedness and does not assert that final theorem.
