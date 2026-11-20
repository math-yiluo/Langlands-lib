# Irreducibility of restricted tensor representations

`Langlands.restrictedTensorIrreducibility` proves
`Langlands.RestrictedTensorIrreducibilityStatement.{uI, uG, uV}`. The
published proposition concerns Hausdorff, locally compact, totally disconnected
local groups `G i` with compact open subgroups `H i`, admissible complex
representations `ρ i`, and nonzero `H i`-fixed reference vectors outside a
finite set `E`. The `H i`-fixed spaces are one-dimensional almost everywhere.
The representation `RestrictedTensor.productRepresentation H ρ E r hr` of
the restricted product is irreducible exactly when every `ρ i` is irreducible.

## Proof

For the implication from local to global irreducibility,
`admissibleSchur_scalarEndomorphism` gives the scalar self-intertwiners of
each local factor. The published `RestrictedTensor.representation_isIrreducible`
then applies. Its finite-stage argument pulls back a nonzero invariant
subspace to a stage that contains a lift of a nonzero vector in the
subspace and a lift of an arbitrary target vector. The pullback is invariant
under the finite product of the local groups acting by the external tensor
product, with each group element extended by the identity outside the stage.
`FiniteTensor.isIrreducible_external` makes this pullback the whole stage,
so the subspace contains the target vector as well.

For the implication from global to local irreducibility,
`RestrictedTensor.isIrreducible_of_isIrreducible_representation` works over
an arbitrary coefficient field. Global irreducibility makes the restricted
tensor space nonzero. Every local space is nonzero because the reference
vectors witness this outside `E`, and a zero factor inside `E` would make
every stage zero. Given a proper nonzero subrepresentation `W` at index `j`,
the proof takes the quotient by `W` there and by zero elsewhere. It enlarges
`E` to `insert j E` so that all destination reference vectors outside the
enlarged exceptional set are nonzero. `RestrictedTensor.map` gives the
induced map, and `map_intertwines` makes its kernel a subrepresentation.
A pure tensor with a nonzero coordinate in `W` at `j` and nonzero
coordinates elsewhere gives a nonzero kernel vector. Choosing the
coordinate at `j` outside `W` instead gives a tensor with nonzero image.
Both tests use `map_pure_of_preserves`, `stage_tprod_ne_zero` and
injectivity of the stage maps `of`. The resulting proper nonzero kernel
contradicts global irreducibility.

## Provenance

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-functions*, Proc. Sympos. Pure
Math. 33, Part 1 (1979), pp. 179–183. Section 2 defines the finite-stage
construction on printed p. 180 (one-based PDF p. 176) and gives the
induced map in numbered assertion (1) on printed p. 181 (PDF p. 177).
Example 2 on p. 181 asserts the irreducibility equivalence. The proofs
above use the published finite-stage theorem and the quotient-kernel
argument from Worker 3657's shared draft for Task 7588.

The registered source is `flath-1979-tensor-products`. The retained volume
has SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
