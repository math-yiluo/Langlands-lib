# The operator algebra after scalar extension

This internal comparison supports the proof of Milne, *Algebraic Groups* (2017),
Proposition 4.19(c), pp. 90–91 (`milne-2017-algebraic-groups`).
`scalarExtensionHom` is the action of the scalar-extended original operator
algebra on the new coordinate space; `extendedAlgebra` is its image.

The finitely many entries of the universal matrix span a finite-dimensional
space. Restricting a ground-field linear functional with values in the larger
field to this space and expanding in a basis expresses its coefficient matrix as
a larger-field linear combination of original coefficient matrices.
Consequently invariance under the original extended operators implies actual
all-test stability after base change. The converse follows from the previously
proved lifted universal tensor-test comparison. Thus actual stable subspaces
after extension are exactly the subspaces preserved by `extendedAlgebra`.

The affine matrix comparison forgets the larger base using the canonical
restriction-of-scalars isomorphism of the same test spectrum. The argument works
for arbitrary affine groups and includes all nonreduced affine test algebras.
