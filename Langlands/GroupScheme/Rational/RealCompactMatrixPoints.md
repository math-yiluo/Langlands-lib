# Matrix coordinates of compact real forms

This module supplies the coordinate comparisons for the compact-form proof. A polynomial in the entries of a matrix and its inverse gives a global function on the represented group by evaluation at the universal point. If the function vanishes on a dense family, its basic open is empty, so it is zero on the reduced scheme.

Extending rational points extends the coefficients of their matrices. The matrix on a rational point of the base-changed group also agrees with the original representation on the corresponding extension-field coefficient point. Naturality of the representation for coefficient maps makes rational-point Galois conjugation entrywise on the matrix.

`HasConjugatorToGaloisFixedPoints` records the matrix witness used for descent. The matrix normalizes the image of the base-changed representation, and conjugation by it makes the images of the given extended points fixed by the coefficient automorphisms.

These are internal consequences of the Library's polynomial coordinates and scalar extension. They supply the matrix comparisons in the proof of the group-scheme consequence of Borel, *Lie Groups and Linear Algebraic Groups*, Sections 5.6–5.7, p. 40.
