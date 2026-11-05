# Smooth pointed-family rigidity and descent

This internal derived helper removes the algebraic rational-point premise from
the existing smooth-family and field-descent arguments using the unconditional
smooth rational density theorem in `PointTopology.SmoothSeparablyClosedDensity`.
It retains the entire affine-line basepoint section with all group parameters.
The field, schemes and morphisms share arbitrary universe `u`.

`PointedCommutatorFamily.family_eq_one_of_smooth` applies the existing theorem
for reduced sources with dense rational points. Smoothness of the nested source
follows from smoothness of the group and affine line. Smooth schemes over fields
are reduced, and smooth schemes over separably closed fields have dense actual
rational sections. These supply both premises without a separate rational-point
statement. The target is separated and all affine-line scheme maps into it are
constant. If the family is the identity along its whole basepoint section, it is
the identity on its whole source.

`family_eq_one_of_sepClosed_extension` pulls the entire source to a separably
closed extension of the ground field. The existing source and affine-line
comparison isomorphisms preserve the whole basepoint section. The preceding
result makes the transported family trivial, and faithful fpqc pullback reflects
that equality over the original field. Smoothness of the source group and
separatedness of the target are preserved by scalar extension.

`VectorFactorPointedFamilies.vector_dimension_pos_of_smooth` projects a
nontrivial pointed family through an actual group-scheme product isomorphism.
If the complement becomes affine-line rigid over the separable closure, the
preceding field-descent theorem makes that projection trivial. A vector factor
of dimension zero would also have trivial first projection, making the original
family trivial by the product universal property. Its nontriviality therefore
forces positive vector dimension. This is a deduction about supplied product
data; it does not construct that product decomposition.
