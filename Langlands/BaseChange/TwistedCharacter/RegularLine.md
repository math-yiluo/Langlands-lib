# Regular points on a matrix line

`eventually_sigmaRegular_on_matrixLine` considers the affine line of
matrices from an invertible matrix over a cyclic algebra to a σ-regular
one. Outside a finite set of base-field parameters, the line gives
invertible σ-regular matrices. The determinant of left multiplication on
the finite-dimensional base-field matrix space is a polynomial in the
parameter. It is nonzero at the first endpoint, so invertibility can fail
at only finitely many parameters.

The proof forms the cyclic norm and the resultant of its characteristic
polynomial with its derivative in polynomial matrix coordinates. The
resultant evaluates to the resultant for the norm at each invertible
point. The norm association theorem identifies its value with the base
resultant. Projecting the polynomial to one residue field of the cyclic
algebra gives a polynomial nonzero at the σ-regular endpoint. Its roots
exclude only finitely many base-field parameters.

`exists_sigmaRegular_of_cyclic` supplies the regular endpoint in every
rank. It uses the base diagonal matrix with entries \(1,\dots,n\).
The entries of its \(l\)-th power are distinct in characteristic zero,
and its scalar extension has cyclic norm associated to that power.

This is a polynomial argument for the generator component used in the
regular-locus comparison of Arthur–Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula*, Chapter 1,
Proposition 2.2, printed pp. 11–12. Source ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
