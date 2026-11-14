# Local equality of parabolics from an actual field-valued point

This internal derived construction extends `relativeParabolicLocalEquality`
from a residue-field fibre to the fibre at any supplied field-valued point of
the base. It retains `RelativeParabolicLieContainmentStatement` as an explicit
premise.

`SubgroupFunctor.range_baseChange_eq_of_factorization` reflects equality of
two monomorphically represented subgroup ranges through a factorization of
base maps when the last map is fpqc. The proof compares the iterated and direct
base changes by `Descent.pullbackComparison`, uses naturality and invariance
of ranges under source isomorphisms, and then applies the published fpqc
reflection of range equality.

For a map from the spectrum of any field, the induced map to the residue field
of its image is a field extension. Its spectrum is fpqc, so equality of the
supplied fibres reflects to equality at that residue field.
`SubgroupFunctor.residueFiber_range_eq_of_fieldPoint_range_eq` implements this
step without assuming the field is algebraically closed.

`relativeParabolicLocalEqualityOfFieldPoint` applies this reflection and the
existing local equality construction. Its inputs are two relative parabolic
inclusions in a reductive group, a common closed fibrewise maximal relative
torus, and equality of their subgroup functors after the specified field base
change. It returns an open neighbourhood of the image of the field point on
which the restricted subgroup functors agree. The conclusion concerns all test
schemes; it requires equality of fibre subgroup functors, rather than just
equality of sets of field-valued points. No Borel conjugacy or unconditional
Lie-containment theorem is asserted.
