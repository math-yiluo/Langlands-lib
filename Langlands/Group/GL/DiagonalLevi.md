# Diagonal units in standard block Levis

This module is a derived construction over every commutative ring `R`, in an
arbitrary universe, and every finite rank `n`. It includes rank zero and every
ordered positive block shape `B : BlockShape n`. No field, topology, or
representation hypothesis is used.

Write `D(a) = (singletons n).blockScalar R a` for a tuple of units
`a : Fin n → Rˣ`. The existing singleton block embedding identifies its underlying
matrix with the diagonal matrix of the entries of `a`.
The existing `leviEmbedding_singletonLevi_val` gives this matrix equality directly
for the definitionally equal singleton block-scalar presentation.
`singletons_blockScalar_apply` exposes the corresponding entry formula.

## Construction and ambient embedding

`B.diagonalLevi R` is a multiplicative map from coordinate unit tuples to the
actual product Levi `B.Levi R`. Its component at block `i` is the diagonal matrix
with entries `a (B.index i j)` as `j` ranges over that block. Multiplication and
identity are preserved because each component is a singleton block-scalar
homomorphism.

`leviEmbedding_diagonalLevi` proves

```text
B.leviEmbedding R (B.diagonalLevi R a) = D(a).
```

The proof tests matrix entries at the block indices supplied by `B.indexEquiv`.
Within one block the existing Levi entry formula and injectivity of `B.index i`
give the diagonal entry formula. Between distinct blocks the Levi entry is zero;
injectivity of `B.indexEquiv` shows the ambient diagonal entry is zero too.

`singletonSplitComponent_le_leviSubgroup` then proves the actual subgroup inclusion

```text
(ConjugateBlockPair.standard (singletons n)).splitComponent ≤ B.leviSubgroup R.
```

An element of the split component has the form `D(a)` by
`ConjugateBlockPair.standard_scalarMap`. The constructed `B.diagonalLevi R a`
is its explicit preimage under the standard Levi embedding.

## Permutation conjugation

The existing convention `permutation n R w` sends the coordinate basis vector
`e_j` to `e_(w j)`. `permutation_conj_singletons_blockScalar` proves

```text
permutation n R w * D(a) * (permutation n R w)⁻¹ = D(fun i => a (w⁻¹ i)).
```

The proof uses the published `permutation_conjugate_entry` and the diagonal
matrix formula. Injectivity of `w⁻¹` identifies the two diagonal conditions.

`permutation_mem_singletonSplitComponent_normalizer` deduces that every such
permutation matrix lies in the normalizer of the actual singleton split
component, as a subset of `GeneralLinear n R`. For one subgroup inclusion, the
new coordinate tuple is `a ∘ w⁻¹`; for the reverse inclusion it is `a ∘ w`.
Thus the result is equality of the actual conjugated subgroup and the original
subgroup, not merely an abstract torus isomorphism.

## Provenance and scope

All content is elementary and derived from the published definitions and entry
formulas in `Langlands.Group.GL.SingletonBlocks`, `Langlands.Group.GL.Maps`, and
`Langlands.Representation.Exponents.ParabolicPair`. No external literature result
is asserted here. These lemmas provide diagonal-torus and permutation facts for
the semistandard Langlands conjugacy proof. They neither classify arbitrary
normalizer elements nor construct a Weyl standardizer for an arbitrary
semistandard pair. No uniqueness or recovery of representation data is claimed.
