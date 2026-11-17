# Finite covariant families inside translation-stable spaces

This is derived supporting work for the independent affine homogeneous quotient
argument. It uses the actual affine coordinate algebra and the published finite
regular representation, together with its all-test basis transformation formula.

`coordinateFamily` forms the family whose j-th section is the linear combination
of the original sections given by column j of a ground-field matrix B. Pullback of
this family along any relative scheme point applies the same scalar-extended
matrix. If B intertwines the original representation with a smaller one on every
relative test, transposing the matrix identity proves covariance of the new
family. Split invariant coordinates give such an intertwiner.

For any affine ambient group J, any actual group morphism i from H to J, and a
finite regular subspace of the coordinate algebra of J, the actual global
sections of a chosen basis form a right-covariant family for the regular
representation restricted along i. The proof uses the published
`affineRegularRepresentation_mul_basis` and the identification of coordinates
with actual global functions.

These constructions retain arbitrary relative test schemes. They do not assume
geometric reductivity or assert affineness of a quotient.
