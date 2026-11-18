# Descent of actual semisimplicity along a field extension

This internal proof concerns the semisimple assertion of Milne,
*Algebraic Groups* (2017), Proposition 4.19(a), pp. 90–91
(`milne-2017-algebraic-groups`). Both hypothesis and conclusion use the unchanged
target's raw sum of simple actual stable subspaces.

The proof converts semisimplicity to the operator-module complemented-lattice
criterion. For each original operator submodule, extend its ground-field
subspace. The semisimple extended operator module supplies a complementary
submodule and the corresponding new-field linear projection.

Both extended subspaces are preserved by every extended original operator, so
that projection commutes with the original operators. Apply a ground-field
linear functional on the extension field that takes one to one to its coordinate
vectors. This yields `descendEndomorphism`: a ground-field linear endomorphism
taking values in the original subspace, fixing that subspace, and commuting with
the original operator algebra. Its kernel is an operator-module complement.
Thus every original operator submodule is complemented, proving semisimplicity.

The supporting constructions `vectorMap` and `coefficientVector` apply the field
map and a coefficient functional coordinatewise. This argument applies to
arbitrary affine group schemes over fields and retains all affine tests.
