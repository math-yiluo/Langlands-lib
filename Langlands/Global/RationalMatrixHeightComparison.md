# Bounding rational adelic matrix heights by entry heights

`Langlands.Global.AdelicMatrixHeight.matrixAndInverseEntry` reads the
entries of an invertible matrix and its inverse using two copies of the
finite entry index set.

The dimension-scaled adelic height of a principal rational matrix of
positive size is at most the product of the scalar multiplicative heights
of these entries times the archimedean dimension factor. At each place
the matrix-and-inverse maximum is at most the product of the maxima
of each entry norm with one. The scalar diagonal norm
identities identify these factors with the corresponding absolute
values of the original number-field entries. Finite support permits
reordering the finite-place products. The archimedean factors use the
same place multiplicities as Mathlib's scalar height.

It follows that a family of rational matrices whose entry heights and
inverse-entry heights have polynomial bounds also has a polynomial
bound on the full adelic height with lower bound one. The constants
multiply and the exponents add over the finite set of entries. At size
zero the lower-bounded height is one, since the dimension scaling
vanishes at an infinite place.

This internal comparison uses the Library's normalized matrix-and-inverse
height, its diagonal scalar norm identities and Mathlib's place formula
for `Height.mulHeight₁`.
