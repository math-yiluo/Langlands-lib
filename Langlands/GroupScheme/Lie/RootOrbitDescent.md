# Fixed-field coordinates on invariant actual root-orbit tuples

This internal construction combines the coherent orbit-line coordinates
with the published finite-Galois orbit coordinate algebra. The coefficient
fields have arbitrary universe `u`; the auxiliary index and vector types
have independent universes.

In `Langlands.LinearAlgebra.OrbitLines`, `invariantSections i W` is the
additive subgroup of dependent tuples `f j` in the subspaces `W j` on one
orbit satisfying `sigma • f j = f (sigma • j)` in the ambient vector
space. The ambient action is additive. Given a linear coordinate `e j`
on every line and its full inter-line equivariance law,
`sectionCoordinateEquiv` applies the inverse coordinate at each index.
The invariance condition is equivalent to the scalar equivariance
condition defining `orbitCoordinateAlgebra`. The inverse applies the
original coordinates pointwise, and both maps preserve addition.

For finite Galois `L/k`, `fixedFieldSectionEquiv` composes this additive
equivalence with the inverse of `orbitEvaluationEquiv`. Its parameter
field is the fixed field of the stabilizer of the original index.
Its value in the `j` line is `e j` applied to the image of the parameter
under the embedding corresponding to `j`. This explicit formula is
`fixedFieldSectionEquiv_apply`.

The actual application uses a maximal torus `j : T.toGrp ⟶ G` of an
affine connected reductive group over `k`. Assume a finite Galois
extension `L/k` splits `T`, and choose an actual root `beta` of `j_L`.
`rootOrbitInvariantSections` consists of tuples in the actual adjoint
weight spaces on the ordinary Galois orbit of `beta`, invariant under
the canonical Lie coefficient transport. The already constructed
`rootOrbitLineEquiv` provides the entire coherent coordinate family and
its Galois law. Thus `rootOrbitFieldSectionEquiv` gives an additive
equivalence from `rootOrbitField k L j beta` to those invariant tuples,
without an input basis, dimension or action on the weight spaces.
The parameter field is an intermediate field of a finite Galois
extension, hence is finite separable over `k`. The theorem
`rootOrbitFieldSectionEquiv_apply` identifies every component using
`rootOrbitEmbeddingEquiv` and the same actual line coordinate.

The provenance is internal: pointwise coherent linear coordinates
translate the invariance equations into scalar equivariance, after
which the existing fixed-field evaluation equivalence applies.
The result describes dependent Lie-space tuples. It does not identify
them with the Lie algebra of an actual rational root subgroup, nor
with that subgroup's rational points. Equality of the Galois orbit
with a relative-root restriction fiber, actual root-group field
coordinates, valuation compatibility and apartment existence remain
separate obligations.
