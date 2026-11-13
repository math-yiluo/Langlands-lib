# Isotropic dimensions under Hermitian hyperbolic splitting

This internal extension of `HermitianHyperbolicReduction` constructs the
restricted middle pairing and coordinates on actual totally isotropic
submodules. It proves that such a submodule has at most half the dimension
of a supplied nondegenerate Hermitian space.

The fields `K` and `L` share an arbitrary universe; the vector space `V`
has an independent universe. The extension `L/K` is separable quadratic,
and conjugation is `SU3Root.fieldInvolution K L`. The pairing `h` is
`L`-linear in its first variable and conjugate-linear in its second, with
`bar (h v w) = h w v`. There is no characteristic restriction.

## Restricted middle pairing

`hyperbolicMiddlePairing h x y` is literally the restriction of `h` in
both arguments to `hyperbolicMiddle h x y`, the intersection of the
kernels of pairing with `x` and with `y`. Its evaluation theorem is
definitional. `hyperbolicMiddlePairing_bar` obtains Hermitian symmetry
by applying the supplied symmetry of `h` to the subtype values.

Assume

```text
h x x = 0, h x y = 1, h y x = 1, h y y = 0.
```

`hyperbolicMiddlePairing_nondegenerate` shows that the restriction is
nondegenerate when `h` is nondegenerate. If a middle vector pairs to zero
with the entire middle, the full hyperbolic coordinate pairing formula
shows that it pairs to zero with every ambient vector: its two endpoint
pairings vanish, and hyperbolic projection fixes it. Left separation for
`h` then makes it zero. Hermitian symmetry converts right separation to
the left separation just proved.

## Coordinates on a totally isotropic submodule

Let `W` be an actual `L`-submodule of `V`, assume
`h a b = 0` for every pair of elements of `W`, and assume `x ∈ W`.
`isotropicMiddle W` is the actual intersection with the hyperbolic
middle, written as the comap of `W` along the middle's subtype map.

For `z ∈ W`, total isotropy makes `h z x = 0`, so the existing
hyperbolic projection reduces to `z - h z y • x`. This remains in `W`
and lies in the middle. `isotropicHyperbolicProjection` restricts the
actual projection accordingly. `isotropicHyperbolicCoordinates` gives
the `L`-linear equivalence

```text
W ≃ₗ[L] L × isotropicMiddle W,
z ↦ (h z y, projection z),
(a, z) ↦ a • x + z.
```

The inverse proofs expand these formulas, using total isotropy,
middle membership, and the four hyperbolic pairing identities.
Under finite dimensionality, `isotropicMiddle_finrank` applies the
dimension formula for a product to obtain

```text
finrank L W = finrank L (isotropicMiddle W) + 1.
```

`isotropicMiddle_totallyIsotropic` checks that the actual intersection
is still totally isotropic for the actual restricted pairing.

## Dimension bound

`two_mul_finrank_le_of_totallyIsotropic` states

```text
2 * finrank L W ≤ finrank L V
```

for every totally isotropic `W` in a finite-dimensional nondegenerate
Hermitian space. Its private auxiliary proof uses strong induction on
the ambient dimension. The zero submodule is immediate. Otherwise,
choose a nonzero `x ∈ W`. The imported `exists_hyperbolic_partner`
constructs an isotropic partner `y` with cross pairings one, using the
trace-one element of the separable quadratic extension, including in
characteristic two. Removing that hyperbolic plane lowers the ambient
dimension by two, preserves nondegeneracy and total isotropy on the
middle, and lowers the dimension of `W` by one. The induction
hypothesis and these two exact dimension equalities imply the bound.

`finrank_le_one_of_totallyIsotropic_of_finrank_le_three` is the
arithmetic consequence that every such `W` has dimension at most one
when the ambient dimension is at most three.

## Provenance and scope

The content is internal elementary linear algebra derived from the
imported hyperbolic splitting constructions, actual submodule maps,
finite-dimensional product formulas and induction. No external
classification statement is being transcribed. The extension, pairing,
Hermitian symmetry and nondegeneracy are inputs. This unit does not
construct a Hermitian presentation of an outer-type-A group scheme or
compare its split rank with the maximal totally isotropic dimension.
