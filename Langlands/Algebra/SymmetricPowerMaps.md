# Linear functoriality of symmetric tensor powers

This internal companion uses the symmetric multilinear universal property to
apply a linear map to every factor in Mathlib's actual symmetric tensor quotient.
`map_tprod` gives its value on pure tensors; `map_id` and `map_comp` give the
identity and composition laws by the pure-tensor spanning property. The
coefficient commutative semiring and index type share a universe, with independent
module universes and no finite-index assumption. No grading or multiplication of
symmetric powers is asserted.
