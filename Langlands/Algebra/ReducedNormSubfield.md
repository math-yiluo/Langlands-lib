# Reduced norm on a field of reduced degree

Let `K` be a field and `A` a finite-dimensional central simple `K`-algebra.
The algebra `A` is only required to be a ring. Let `L` be a finite field
extension of `K` and `ι : L →ₐ[K] A` an actual algebra embedding.
The types `K` and `A` share an arbitrary universe; `L` has an independent
arbitrary universe. All characteristics are allowed, and separability of
`L/K` is not assumed.

`Langlands.CentralSimple.reducedNormOnSubfield K A ι` is the multiplicative
homomorphism on `L` obtained by composing `ι`, the original-element
inclusion into `K ⊗[K] A`, and the existing canonical reduced norm. It
requires no supplied norm law or comparison hypothesis.

If `[L : K] = reducedDegree K A`, the module proves

```text
reducedCharpoly K A (ι a) = (Algebra.lmul K L a).charpoly
reducedNorm K A K (1 tensor ι a) = Algebra.norm K a
reducedNormOnSubfield K A ι = Algebra.norm K.
```

These are the declarations `reducedCharpoly_eq_field_charpoly`,
`reducedNorm_eq_field_norm`, and `reducedNormOnSubfield_eq_norm`.
The degree hypothesis is explicit; no existence of such an embedding
is asserted.

The contribution is an internal deduction from the imported canonical
reduced norm and reduced characteristic polynomial, the regular
characteristic-polynomial power formula, and Mathlib's finite-dimensional
linear algebra. It introduces no new external theorem or source assertion.

The helper `charpoly_blockDiagonal` proves that a block diagonal matrix
has characteristic polynomial equal to the product of the characteristic
polynomials of its blocks. Matrix extensionality identifies its
characteristic matrix with the block diagonal of the individual
characteristic matrices, and the determinant formula for a block
diagonal matrix gives the result.

For `K → L` and a compatible `L`-module `M`, the helper
`toMatrix_restrictScalars_smul` computes the matrix of scalar multiplication
by `x : L`, viewed as a `K`-linear map. A tower basis formed from a
`K`-basis of `L` and an `L`-basis of `M` gives a block diagonal family
of copies of the field multiplication matrix of `x`, up to the displayed
permutation of the product indices.

When all three relevant modules are finite-dimensional,
`charpoly_restrictScalars_smul` therefore identifies the characteristic
polynomial of this restricted scalar operator with the characteristic
polynomial of multiplication by `x` on `L`, raised to `[M : L]`.
Characteristic polynomial is invariant under the matrix reindexing and
under taking the matrix of a linear map in a basis.

For the main comparison, `A` is given the `L`-module structure defined by
left multiplication through `ι`. This does not require an `L`-algebra
structure on `A`: the embedded field need not be central. The scalar tower
law follows from the `K`-linearity of `ι`, and finite-dimensionality over
`L` follows from finite-dimensionality over `K`. The tower dimension law,
the hypothesis `[L : K] = reducedDegree K A`, and the existing positive
degree-square formula give `[A : L] = reducedDegree K A`.

Left multiplication by `ι a` on `A` is the restriction of scalar
multiplication by `a` in this module structure. The preceding helper
expresses its characteristic polynomial as the reduced-degree power of
the field characteristic polynomial. The imported
`charpoly_leftMulMatrix_eq_reducedCharpoly_pow` expresses the same regular
characteristic polynomial as the reduced-degree power of the canonical
reduced characteristic polynomial. Both polynomials are monic and the
reduced degree is positive. The imported
`Langlands.Polynomial.eq_of_monic_pow_eq` cancels these powers, proving the
characteristic-polynomial equality.

To obtain the norm equality, the proof applies that equality to `-a` and
evaluates at zero. The imported `reducedCharpoly_eval` turns the left
side into the reduced norm of `1 tensor ι a`. Mathlib's
`LinearMap.eval_charpoly` turns the right side into the determinant of
multiplication by `a`, which is the definition of `Algebra.norm K a`.
Finally, homomorphism extensionality gives the equality of multiplicative
homomorphisms.

This result does not construct a field of reduced degree, an unramified
or cyclic maximal subfield over a local field, or a factorization of
arbitrary division-algebra units modulo commutators. Local SK1 vanishing
and `LocalKneserTitsStatement` remain separate proof obligations.
