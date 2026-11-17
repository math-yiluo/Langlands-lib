# Finite-coordinate matrices for the regular representation

Let `Q` be a finite group over a field `k`, with both types in a common universe.
Enumerating `Q` identifies its function space `Q → k` with
`Fin (Fintype.card Q) → k`. The construction `coordinateRegular` transports
Mathlib's function regular representation through this linear equivalence.
The homomorphism `regularMatrixHom` is its invertible matrix form.

The lemma `regularMatrixHom_mulVec` identifies matrix-vector multiplication
with the transported regular action. An explicit order isomorphism of
subrepresentation lattices shows that semisimplicity is unchanged by the
coordinate enumeration. The regular-representation order criterion therefore
holds in these finite coordinates, both as nonvanishing of `Nat.card Q` in the
field and as nondivisibility by its characteristic.

This is internal coordinate infrastructure for realizing a finite component
quotient's regular representation as an actual group-scheme representation.
It is derived from Mathlib's regular representation, linear conjugation and
matrix-to-linear-map equivalence, together with the regular order criterion
proved in `Langlands.Representation.FiniteRegularSemisimplicity`.
