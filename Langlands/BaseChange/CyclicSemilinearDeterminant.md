# Determinant of a cyclic semilinear defect

This module supplies the algebraic scalar-extension step needed for the twisted
relative discriminant comparison. It is an internal derivation, not a transcription
of a character or orbital-integral theorem. The motivating comparison is in
Henniart–Lemaire (2011), II.4.5, printed p. 88, just before formula (3).

## Interface

Let `E/F` be a cyclic field extension of degree `l` in the sense of the published
`IsCyclicAlgebra σ l`. For a finite coordinate set `ι`, `coordinateFieldAut σ ι`
is the `F`-linear map on `ι → E` given by `x ↦ (i ↦ σ(x i))`. Its pointwise formula is
`coordinateFieldAut_apply`.

For a square matrix `A` acting on column vectors, `IsCyclicAlgebra.det_cyclicSemilinearDefect`
proves

\[
 (\operatorname{algebraMap}_{F,E})\bigl(\det_F(1-A\circ\sigma)\bigr)
 = \det_E\bigl(1-A\sigma(A)\cdots\sigma^{l-1}(A)\bigr).
\]

On the left, `A` is interpreted as its `E`-linear column action and then restricted
to `F`; multiplication of endomorphisms is composition. On the right, `σ` acts on
matrix entries, and the list product uses increasing exponents, starting with zero.
The fields and the coordinate set have independent universes. No invertibility of
`A`, characteristic-zero assumption, or topological hypothesis is required.

## Proof implemented in Lean

1. `IsCyclicAlgebra.isGalois` supplies the finite Galois extension. The powers of
   `σ` indexed by `Fin l` are distinct by the order condition and exhaust the
   automorphism group by its cardinality. Every `F`-embedding of `E` into itself is
   an automorphism.
2. `TensorProduct.piRight` distributes `E ⊗[F] (ι → E)` over the finite coordinate
   set. The separable embedding-evaluation theorem identifies each `E ⊗[F] E`
   with functions on embeddings into `E`. Reindexing the embeddings by powers
   of `σ` and exchanging the two function arguments gives a linear equivalence
   with `Fin l → ι → E`. At `(i,j)` the image of `c ⊗ x` is `c * σ^i(x j)`.
3. On pure tensors the extended defect becomes the weighted cyclic defect with
   weight `σ^i(A)` at index `i` and input from `finRotate l i`. This follows by
   expanding the matrix-vector product, and the final index wraps because `σ^l = 1`.
   Tensor induction extends the equality to every tensor.
4. Determinants commute with scalar extension and are invariant under linear
   conjugation. `Langlands.Algebra.det_weightedCycleDefect` now gives the determinant
   of the defect of the ordered weight product. The matrix-to-endomorphism algebra
   equivalence respects products and identifies its determinant with the matrix
   determinant.

This is only the coordinate determinant identity. In particular it does not
identify the adjoint determinants on a Levi Lie quotient, compare Haar measures,
or prove descent or the induction theorem.
