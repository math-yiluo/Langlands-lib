# Linear maps from actual symmetric tensor powers

This internal construction supplies the linear universal property for Mathlib's
actual symmetric tensor power, defined as the additive quotient of the indexed
tensor power by permutation relations.

`Langlands.Algebra.SymmetricTensors.lift` descends a multilinear map that is
invariant under every permutation of its indices. The tensor universal property
first gives a linear map on the tensor power. Symmetry puts the generators of
the defining additive congruence in its kernel. The additive quotient lift
therefore exists, and quotient induction proves scalar compatibility.

`lift_tprod` gives the exact value on symmetric pure tensors.
`linearMap_ext` uses the published spanning theorem for those tensors, and
`lift_unique` proves uniqueness from the prescribed pure-tensor values.
The coefficient ring can be any commutative semiring and no finite-index
hypothesis is required. As in Mathlib's current `SymmetricPower`, the coefficient
semiring and index type share a universe; the source and target modules may
occupy independent universes.

The provenance is internal: this is an explicit consequence of the defining
quotient and the tensor universal property, supplied to support later
enveloping-algebra symmetrization. It does not construct that symmetrization,
identify symmetric powers with graded pieces, or prove the automorphic growth
statement.
