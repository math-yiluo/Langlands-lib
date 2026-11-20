# Base change of tensor-unit primitives

Take fields `K` and `B` over `F` and a specified `K`-algebra isomorphism
`K ⊗[F] B ≃ₐ[K] D` to a field `D`. For a coefficient field `M` over `K`
with its compatible `F`-algebra structure, `baseChangeTensorUnitEquiv`
identifies the units of `B ⊗[F] M` with those of `D ⊗[K] M`. This uses
the canonical associativity comparison followed by the indicated
isomorphism on the left tensor factor. The equivalence intertwines
coefficient automorphisms over `K`. If `B/F` and `D/K` are finite,
it preserves the actual determinant norm.

Suppose `M` also contains `L` compatibly over `F`, with `L/F` Galois.
Transfer of cochains first extends the right tensor factor to `M`,
then uses the above equivalence. Restriction of automorphisms and
naturality of the determinant norm show that the transferred
cochain has the transferred degree-two differential and the
extended scalar norm.

For the comparison theorem assume characteristic zero, that `M/K`
is finite Galois, and that the finite separable `D/K` is embedded
over `K` in `M`. If an `n`-torsion primitive over `L` has scalar
Kummer norm and the transferred differential admits a norm-one
`n`-torsion primitive over `M`, the base radicand after extension
to `K` is a norm modulo powers from `D/K`. The proof transfers
both the original primitive and its scalar radical, then applies
the fixed-unit comparison. This is an internal calculation for
the local norm condition at the nonsplit places.
