# Determinant of a weighted cyclic shift

Let `V` be a vector space over a field `K`. Given `d` endomorphisms
`A : Fin d → Module.End K V`, `weightedCycleDefect A` is the endomorphism of
`Fin d → V` with component

\[
  x_i-A_i x_{i+1\bmod d}.
\]

For `d > 0` and `V` finite-dimensional, `det_weightedCycleDefect` proves that
its determinant is

\[
  \det_K(1-A_0 A_1\cdots A_{d-1};V).
\]

The Lean theorem uses a cycle of length `d + 1`, and the product is
`(List.ofFn A).prod`, taken in increasing index order with multiplication of
endomorphisms by composition. The weights need not commute or be invertible.

## Implemented proof

The case of one component is evaluation at the unique index. For a longer
cycle, split off the last component, writing the coordinates as `(x, y)`. The
last output is `y - A_last (x 0)`. Precompose with the determinant-one lower
block shear `(x, y) ↦ (x, A_last (x 0) + y)`. The last output is then `y`.
On the preceding coordinates, the only changed edge connects their last
component back to their first, with weight `A_penultimate * A_last`. The
remaining dependence on `y` lies in the upper-right block. The determinant is
therefore that of the shortened cycle, with the same ordered product. The
proof uses the determinant of an upper block triangular matrix in product
bases; the lower block case follows by swapping the two factors.

## Provenance and scope

This is an elementary linear-algebra lemma derived for the cyclic
base-change discriminant comparison. After splitting a cyclic field extension
by its embeddings, a semilinear endomorphism becomes a weighted shift of this
form. The file proves only the determinant computation on the split product;
it does not perform the field-extension step or prove any discriminant or
orbital-integral comparison.
