# Full automorphic maps on actual algebraic coefficient cohomology

Fix the full coefficient module `Space e ρ` attached to the original
general-linear product scheme representation. A full automorphic operator
intertwiner `L : S.Intertwiner T` induces maps on the original algebraic
coefficient horizontal complex, its actual differential kernels and its
cycle quotients. These maps retain the existing finite adelic representations.

`tensorAlgebraicIntertwinerReducedLieHom` tensors `L` with the identity on the
fixed coefficient module and restricts the existing full tensor Lie map
through the actual reduced Lie algebra inclusion. Its value on `f ⊗ v` is
`L f ⊗ v`. The compact tensor map has the same underlying linear map.
`tensorAlgebraicHorizontalMap` is the existing horizontal tensor map with
the identity compact coefficient intertwiner. Its value is postcomposition
by this same reduced Lie map. Finite equivariance comes from the existing
full automorphic tensor map.

`tensorAlgebraicHorizontalMap_differential` proves commutation with the
original algebraic horizontal differential by coefficient differential
functoriality. It supplies the chain equation to the existing
`Horizontal.mapCyclesIntertwiner` and `Horizontal.mapCohomologyIntertwiner`.
The resulting `tensorAlgebraicHorizontalCyclesMap` and
`tensorAlgebraicHorizontalCohomologyMap` act on the already constructed
kernel and cycle quotient; they introduce no replacement cohomology carrier.
The cycle value and quotient class formulas retain the original transported
representative. The quotient projection is natural as a bundled finite
adelic intertwiner.

The cochain maps preserve identity and composition by the tensor-product
linear-map identity and composition laws. The generic congruence helpers in
`HorizontalCohomologyIntertwinerLaws` carry those actual cochain equalities
to both cycles and cohomology. Thus all three levels preserve identity and
composition as equalities of bundled finite adelic intertwiners.

The cycle value, quotient class, quotient-projection naturality, and cycle
and quotient identity/composition declarations are inferred-type
abbreviations of the specialized generic proofs. Their conclusions use the
generic definitions underlying the named actual maps and representations;
these are definitionally the same objects. This preserves the formulas
without restating and rechecking large definitionally equal target types.
The abbreviations add no assumptions.

The field universe is independent of the small finite coefficient and
embedding index types. Both complex-place orientations, empty finite index
types, the entire original coefficient carrier and every natural degree
are retained. The reduced tensor map and horizontal cochain functoriality
hold in all ranks. The differential, cycle and quotient constructions
retain the explicit `NeZero n` hypothesis of the published horizontal
complex. This module asserts no topology, occurrence or nonvanishing
property of cohomology.

This is an internal construction from the published original coefficient
horizontal comparison, tensor maps and generic horizontal cohomology
transport. It makes no new original-literature identification. All chain
compatibility used for descent is proved from the actual reduced Lie map.
