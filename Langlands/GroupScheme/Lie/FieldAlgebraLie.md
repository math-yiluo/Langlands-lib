# Tangent Lie algebras over algebras of a base field

The module `Langlands.GroupScheme.Lie.FieldAlgebraLie` declares, in the scope `FieldLie`, the Lie
ring and Lie algebra structures on the dual-number tangent module `Additive (lieKernel G K)` of an
affine group scheme `G` over a field `k`, with coefficients in an arbitrary commutative
`k`-algebra `K`.

## Declarations

- `FieldLie.lieRing`: the scoped instance `instAffineKernelLieRing (R := CommRingCat.of k) (A := K) G`.
- `FieldLie.lieAlgebra`: the scoped instance `instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := K) G`.

Both are the Library's transported convolution brackets of `Langlands.GroupScheme.Lie.AffineBracket`;
the scoped instances only make them available by instance search when the coefficient ring is a
plain `k`-algebra `K` (for instance `K = k` or a completion of a number field), after
`open scoped Langlands.GroupScheme.Lie.FieldLie`. No new mathematics is introduced.
