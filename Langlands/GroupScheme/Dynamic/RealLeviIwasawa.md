# Real Levi-compatible Iwasawa from ambient star realization

Author: Worker 1655.

This internal construction uses the polynomial adjoint core to obtain
internal Hermitian cocharacter conjugation from adjoint stability of the
actual base-field image. The coefficient field is real `RCLike`, and a
compatible algebraically closed `RCLike` extension is supplied. The
extension image itself need not be adjoint-stable. All fields have common
arbitrary universe `u`.

The finite-support separating two-power root of unity belongs to the
extension. Its cocharacter value lies in the polynomial adjoint core by
`cocharacterUnitsHom_mem_starCore`. This core is adjoint-stable and
polynomially defined, so internal real two-power unitarization applies.
The resulting conjugator is entrywise real and belongs to the core,
hence to the original extension image. Descending its matrix and inverse
and reflecting the closed-image equations give a conjugator in the
actual base-field image. Unitarity at the separating root makes all
extended weight projectors Hermitian; scalar-extension reflection makes
the original projectors Hermitian.

The provenance is internal composition of the polynomial adjoint core,
internal real unitarization, and actual closed-image descent. It does not
establish initial ambient realization or common-cocharacter existence for
an arbitrary rational pair. The unconditional host statement remains open.

`MatrixRepresentation.realHermitianConjugate` chooses the resulting
internally conjugated representation. Its specification proves that it
is a closed immersion, has Hermitian weights for the original
cocharacter, and has exactly the original actual base-field matrix-point
image. The definition uses the internal conjugator just constructed;
it asserts no uniqueness. Since the image is unchanged, its original
base-field adjoint stability remains valid.

The three `HasClosedStarRealization.hasReal…` theorems apply this choice
to an ambient closed star realization. The same supplied cocharacter
still has dynamic parabolic and centralizer represented by the supplied
maps `p` and `m`. The first theorem supplies Hermitian star Levi
realization. Unitary diagonalization then gives compatible diagonal
realization. With ambient affineness, the existing diagonal polar
construction gives a compact subgroup with all four conclusions:
ambient maximal compactness, coverage with parabolic image on the left,
equality of its parabolic and Levi intersections, and maximal
compactness of its inverse image in the specified Levi point group.
These are the original actual affine-point groups and point
homomorphisms with their regular-function evaluation topologies.

The extension field, algebraic closure instance and compatible real
scalar tower are explicit inputs here. These theorems do not assert
that a base-field star-stable image is star-stable after extension. The
polynomial adjoint core supplies the subgroup needed for this particular
cocharacter instead. Choosing a suitable extension and combining the
real and complex coefficient cases remain a separate assembly step.
