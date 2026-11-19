# Cancellation of a nonzero quadratic line

Worker 864.

`Langlands.quadraticForm_equivalent_of_prod_smul_sq` proves one-dimensional
Witt cancellation over a field in which 2 is invertible. An isometry between
orthogonal products with the common summand `a • QuadraticMap.sq`, for `a ≠ 0`,
yields an isometry between the remaining forms. The remaining forms can have
radicals and can live on different vector spaces.

The proof uses `Module.reflection` with the polar functional divided by the
value of the reflecting vector. The quadratic addition formula proves directly
that the reflection preserves the form. Two vectors with the same nonzero value
are carried to each other by the reflection in their difference when its value
is nonzero, or by the negative of the reflection in their sum otherwise.

The original isometry is composed with such an isometry to fix `(1, 0)`.
Pairing with `(1, 0)` in either product gives `2 * a` times the first coordinate,
so the isometry and its inverse preserve the second factor. Restricting them
produces inverse linear maps that preserve the remaining forms.
