# A finite bound for the ranks of actual split subtori

Worker 1274. This is an internal derivation from the published actual
dual-number identity kernels, their module structures, affine coordinate
algebras, and split-torus points. It uses no conjugacy or rank-attainment
hypothesis.

Postcomposition by a group-scheme homomorphism restricts to a linear map
`Lie.targetMapLinear` on the actual identity kernels. A monomorphism on the
underlying schemes makes that linear map injective, by cancellation.
For a split torus, each vector of coefficients gives the actual point whose
unit coordinates are `1 + ε v_i`; this gives an injective linear map from
`I → k` into its identity kernel.

For an affine finite-type group over a field, choose finitely many algebra
generators of its published coordinate algebra. Evaluation of the corresponding
identity derivations on these generators is injective, since derivations
agreeing on algebra generators agree everywhere. Thus its actual Lie kernel
is finite dimensional.

Composing the split-torus coefficient map with postcomposition gives
`Nat.card I ≤ Module.finrank k (Additive (lieKernel G k))` for every closed
split torus. Taking the exact published supremum proves
`splitRank_le_finrank_lieKernel`. This supplies a finite bound and does not
assert maximal extensions or equality with the rank of a maximal torus.
