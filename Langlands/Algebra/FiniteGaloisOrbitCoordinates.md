# Semilinear coordinates on a finite Galois orbit

This internal algebraic construction extends the published
`FiniteGaloisOrbits` module. Let `L/k` be finite Galois, let its Galois group
act on a type `I`, and choose `i : I`. The coefficient fields have arbitrary
universe `u`, and `I` has an independent universe `v`. No finiteness assumption
on `I` is required.

`orbitCoordinateAlgebra k L i` is the `k`-subalgebra of functions from the
orbit of `i` to `L` satisfying `f (σ • j) = σ (f j)`. Algebra operations are
pointwise. The existing field `stabilizerField k L i` is the fixed field of
the stabilizer of `i`. Evaluation at the original point defines
`orbitEvaluation` into that field: an element of the stabilizer fixes the
value by the function's equivariance.

`orbitCoordinates` constructs the inverse from the existing equivalence
between orbit points and embeddings of the stabilizer field into `L`.
It sends `x` to the function `j ↦ orbitEmbeddingEquiv k L i j x`.
The proof of its equivariance uses the published postcomposition formula
for the inverse embedding equivalence. At the original point the embedding
is the inclusion of the fixed field, so evaluation recovers `x`.
Conversely, an equivariant function is determined by its value there:
every orbit point is a Galois translate of the original point.

`orbitEvaluationEquiv` packages these two algebra homomorphisms as a
`k`-algebra equivalence, with the inverse coordinate formula recorded by
`orbitEvaluationEquiv_symm_apply`. Its linear and additive equivalences are
available through the usual algebra-equivalence API.

The provenance is internal: the construction is derived from the existing
finite-Galois orbit/embedding equivalence and pointwise algebra laws. It
does not identify any actual algebraic root subgroup with this coordinate
algebra. Transitivity of an actual absolute-root restriction fiber and a
compatible trivialization of its root lines remain separate geometric
obligations, as do actual R1 field coordinates and the apartment-existence
theorem.
