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

The finite-dimensional kernel instance is reused from `Lie.FiniteDimensional`.
Its proof evaluates identity derivations on finitely many generators of the
affine coordinate algebra; derivations agreeing on those generators agree
everywhere. The duplicate theorem with an explicit field argument is removed,
and callers use the existing instance with its implicit field argument.

Composing the split-torus coefficient map with postcomposition gives
`Nat.card I ≤ Module.finrank k (Additive (lieKernel G k))` for every closed
split torus. Taking the exact published supremum proves
`splitRank_le_finrank_lieKernel`. This supplies a finite bound and does not
assert maximal extensions or equality with the rank of a maximal torus.

The general identity-kernel target maps and their elementary compatibility
lemmas are reused from `Langlands.GroupScheme.Lie.KernelTargetMaps`. Their
public names and argument conventions are preserved.
