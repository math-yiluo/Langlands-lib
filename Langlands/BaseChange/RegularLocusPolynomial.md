# A coordinate polynomial for the σ-regular locus

The theorem gives a nonzero polynomial over the base field in any finite
basis of the matrix algebra. On invertible matrices, its nonvanishing is
equivalent to the Library predicate `IsSigmaRegular`.

The fixed-size resultant of the characteristic polynomial and its derivative
commutes with scalar maps. Over the base field it vanishes exactly when the
characteristic polynomial is inseparable. The fixed size uses the monicity
of the characteristic polynomial and works when its derivative drops degree.
For a matrix over the cyclic algebra, the proof forms the symbolic ordered
product from the Library norm, using the basis coordinates as indeterminates.
It applies a linear retraction of the scalar inclusion to the coefficients
of the symbolic resultant. Evaluation at base-field coordinates commutes with
this retraction. Norm existence and conjugacy invariance of the characteristic
polynomial identify the value on a unit with the ordinary resultant of an
associated matrix.

The proof witnesses nonvanishing at a diagonal matrix over the base field whose
entries have pairwise distinct `l`-th powers. Each fiber of the `l`-th power
map on the infinite field is finite because it is the root set of a nonzero
polynomial. The characteristic polynomial of the norm of the diagonal matrix
then has distinct linear factors. This is an internal polynomial argument for
the Haar conullity of the σ-regular locus used in Henniart–Lemaire 2011, I.5.1
and II.1.3.
