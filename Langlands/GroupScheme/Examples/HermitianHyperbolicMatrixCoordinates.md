# Matrix coordinates for a hyperbolic Hermitian splitting

Author: Worker 176.

This internal construction converts the product coordinates of
`HermitianHyperbolicReduction` into function coordinates on the existing
`HermitianRoot.Index`, and then into an actual invertible Gram-congruence
matrix. It supports the outer-type-A identification task. The Hermitian
pairing and its rank bound are supplied inputs; constructing them from a
group scheme and its Tits index remains a separate obligation.

The elementary matrix declarations work over a commutative ring `A` and
any finite middle index type `ι`. The rank-one applications use fields
`K L : Type u`, a separable quadratic extension `L/K`, its published
`SU3Root.fieldInvolution K L`, and a vector space in an independent universe.
There is no restriction on the field characteristic.

`indexProductCoordinates` is the explicit linear equivalence

```
(Index ι → A) ≃ₗ[A] A × ((ι → A) × A).
```

It evaluates a function at the top, middle and bottom indices. Its inverse
assembles those three pieces by the sum eliminators. The inverse and
linearity identities follow directly from these formulas.

For a diagonal form `H`, the three `gram_mulVec_*` lemmas compute
multiplication by the actual `HermitianRoot.gram H`: the top coordinate
is the original bottom coordinate, the middle coordinate `i` is
`-H.weight i * z i`, and the bottom coordinate is the original top
coordinate. Consequently `gram_mulVec_pairing` proves

```
bar(w) · (gram H * z)
  = z_top * bar(w_bottom) - H.pairing z_middle w_middle
      + z_bottom * bar(w_top).
```

Here matrix multiplication on a vector is `Matrix.mulVec` and the dot is
`dotProduct`. This convention is linear in `z` and conjugate-linear in
`w`. The proof expands the finite sums over the three index pieces,
factors out the negative middle sum, and rearranges commutative products.
In particular, it retains the negative middle sign of the existing Gram
matrix.

`linearCoordinateMatrix e` sends a linear automorphism of `Index ι → A`
through Mathlib's linear-map-to-matrix algebra equivalence. It is an
element of `Matrix.GeneralLinearGroup`, so its invertibility is part of
the constructed object. Its `(i,j)` entry is `e (Pi.single j 1) i`, and
its multiplication on a vector is exactly `e`.

`gramCongruence_of_pairing_coordinates` starts with a matrix `J`, a
diagonal form `H`, and a linear automorphism `e` such that

```
bar(w) · (J * z) = bar(e w) · (gram H * e z)
```

for every pair of vectors. For `P = linearCoordinateMatrix e` it proves
the matrix equality `bar(P)ᵀ * gram H * P = J`. Entrywise expansion and
interchange of two finite sums identify the left side with the pairing
on the images of two standard basis vectors. The assumed pairing
identity reduces this to the corresponding entry of `J`.

`exists_rankOne_gram_coordinates` assumes a finite-dimensional,
nondegenerate Hermitian pairing `h`, a nonzero isotropic vector, a bound
of one on the dimensions of all actual totally isotropic submodules,
and `finrank L V = m + 2`. It produces an anisotropic diagonal form
`H` on `Fin m` and a linear equivalence
`e : V ≃ₗ[L] (Index (Fin m) → L)` with

```
h v w = bar(e w) · (gram H * e v).
```

The proof composes the previously constructed product coordinates with
the inverse of `indexProductCoordinates`, and applies the Gram-pairing
formula above.

Finally, `exists_rankOne_gram_congruence` assumes that the vector space
already is `Index (Fin m) → L` and that `J` gives its full pairing.
Under the same nondegeneracy, isotropic-vector and total-isotropy-bound
hypotheses it produces `H`, its anisotropy proof, and an actual invertible
matrix `P` satisfying `bar(P)ᵀ * gram H * P = J`. The ambient dimension
is computed from the finite index type; the preceding coordinate theorem
and congruence lemma supply the conclusion.

These are derived elementary linear-algebra results. Their provenance is
the explicit constructions described here and the imported hyperbolic
reduction, rather than an appeal to a classification theorem. They do
not assert a group-scheme presentation, an equality between Witt index
and split rank, or the outer-type-A classification target.
