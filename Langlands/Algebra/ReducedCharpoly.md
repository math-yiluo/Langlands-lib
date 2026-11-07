# Reduced characteristic polynomial

For a finite-dimensional central simple algebra `A` over a field `K`,
`Langlands.CentralSimple.reducedCharpoly K A a` is the polynomial

```text
reducedNorm K A K[X] (X ⊗ 1 - 1 ⊗ a).
```

The reduced norm is the Library's canonical reduced norm on the actual
tensor algebra. The common universe of `K` and `A` is arbitrary, and
characteristic is unrestricted. The polynomial is monic and has natural
degree `reducedDegree K A`. These conclusions require no supplied
splitting field or additional structural premise.

This module is an internal consequence of the existing reduced-norm
construction and its regular-representation comparison. It imports
`Langlands.Algebra.ReducedNormRegular`, Mathlib's matrix characteristic
polynomial coefficients and its unique-factorization multiplicity API.
It introduces no assertion from external literature.

For any field extension `L` of `K` with an actual algebra equivalence

```text
e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A))
                              (Fin (reducedDegree K A)) L,
```

`reducedCharpoly_map_chart` proves that mapping the coefficients to `L`
gives the ordinary characteristic polynomial of `e (1 ⊗ a)`. Here the
universe of `L` is arbitrary and independent. The proof uses reduced-norm
naturality for the coefficient map `K[X] →ₐ[K] L[X]`, followed by its
determinant formula for the supplied chart. The splitting map sends the
generic tensor difference to the matrix `X • 1 - (e (1 ⊗ a)).map C`,
which is the usual characteristic matrix. Matrix extensionality verifies
this equality entry by entry.

The monicity and degree theorems use the constructed
`finiteGaloisSplittingField K A` and its actual splitting chart.
Monicity descends along the injective coefficient map. The degree is
preserved under the coefficient map because the original polynomial is
monic; the ordinary matrix characteristic polynomial has degree equal
to the cardinality of its index type.

`reducedCharpoly_eval` proves, for every `t : K`,

```text
(reducedCharpoly K A a).eval t =
  reducedNorm K A K (t ⊗ 1 - 1 ⊗ a).
```

This follows from the same naturality law applied to the evaluation
algebra map `Polynomial.aeval t`.

The helper `leftMulMatrix_generic_sub` works more generally for any ring
algebra over a commutative ring, supplied with a finite basis `b`. In
the base-changed basis over `K[X]`, the matrix of multiplication by
`X ⊗ 1 - 1 ⊗ a` is the characteristic matrix of
`Algebra.leftMulMatrix b a`. The proof distributes the tensor product
multiplication and evaluates the base-changed basis coordinates.
Applying the regular/reduced norm comparison to this tensor element
then proves `charpoly_leftMulMatrix_eq_reducedCharpoly_pow`: the full
left-regular characteristic polynomial of `a` is
`reducedCharpoly K A a ^ reducedDegree K A`.

Finally, `Langlands.Polynomial.eq_of_monic_pow_eq` proves that if monic
polynomials `p` and `q` over any field satisfy `p ^ n = q ^ n`, where
`n` is a nonzero natural number, then `p = q`. Unique factorization
reflects divisibility from these powers in both directions, so the
polynomials are associated. Monicity makes associated polynomials
equal. This cancels powers of monic polynomials; it makes no assertion
that powers of field elements can be cancelled.

These results supply characteristic-polynomial tools for a future
subfield norm comparison. The module does not establish that comparison,
construct local maximal subfields, prove local SK₁ vanishing, or prove
the local Kneser–Tits statement.
