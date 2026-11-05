# The actual adjoint determinant vector in an ambient exterior representation

This internal construction uses the actual Lie inclusion of a represented
dynamic unipotent subgroup into its ambient affine group. Write `N` and `d`
for the supplied finite natural coordinate dimensions of the ambient Lie
kernel and the unipotent Lie kernel. The definition
`Dynamic.adjointExteriorRepresentation` is the exterior power of degree `d`
of the actual ambient adjoint matrix representation, with matrix index
`Set.powersetCard (Fin N) d`.

The coefficient base is an arbitrary commutative ring. The represented
dynamic parabolic and unipotent subgroups and finite natural Lie coordinate
systems are explicit inputs. Both ambient and unipotent structure morphisms
are affine. For the algebraic determinant character, the parabolic scheme
is affine as well. No splitness, reductivity, smoothness, positive dimension
or characteristic hypothesis is imposed in this unit.

`lieInclusionCoordinates` writes the actual differential of the unipotent
inclusion in the two coordinate systems. `adjointExteriorVector` wedges
the images of the standard unipotent Lie basis, and
`adjointExteriorCoordinates` expresses that exterior vector in the standard
exterior basis of the ambient coordinate module. The latter's coordinates
are exactly the minors of the inclusion matrix. Naturality of the given
Lie coordinates and of postcomposition proves naturality of the inclusion.
The determinant formula for the minors then proves that the exterior
coordinate vector commutes with every coefficient algebra homomorphism.
These identities include nonreduced test algebras.

The two nonzero lemmas assume that the underlying unipotent inclusion is
a monomorphism and that the test algebra is a field, expressed by an
explicit `IsField` witness. A monomorphism makes the actual Lie inclusion
injective. Over a field, exterior powers preserve injectivity. The standard
top wedge of the source basis is nonzero because its dual exterior
functional evaluates to one. Its image is the constructed vector, which
is therefore nonzero; the exterior basis equivalence preserves this
property. This also covers `d = 0`. No nonzero claim over an arbitrary
coefficient ring is made.

The action proof first differentiates actual parabolic conjugation with
orientation `p*u*p⁻¹`. Postcomposition with the unipotent inclusion
intertwines the unipotent Lie action and the ambient adjoint action. In
finite coordinates this is an intertwiner of finite free modules. The
helper `Chevalley.exteriorPower_map_image_basis` proves that the image of
a top basis wedge is an eigenvector of the ambient exterior endomorphism
with scalar equal to the determinant of the source endomorphism. It uses
the published `Chevalley.alternatingMap_eq_det_smul` basis determinant
identity for a top degree alternating map, valid
over arbitrary commutative rings. Conjugation invariance identifies the
coordinate determinant with the determinant of the actual Lie action.
The published `adjointDeterminantCharacter_affinePoints` formula identifies
that scalar with the actual algebraic parabolic adjoint determinant
character, on every affine test algebra.

The helpers `Chevalley.exteriorRepresentation_affineMatrix` and
`Chevalley.exteriorRepresentation_affineAction` connect this exterior
linear action with the actual group scheme exterior representation. The
first uses the affine point formula for a corepresented group scheme map;
the second uses the standard matrix formula for a linear map in a basis.
Consequently `adjointExteriorCoordinates_character_action` is an identity
for the actual matrix representation acting on the constructed coordinate
vector, with the published determinant character as its scalar.

The provenance is internal: the construction combines the Library's actual
Lie inclusion, adjoint representation, finite coordinates, exterior matrix
representation and determinant character with the proved elementary
exterior algebra lemmas. It supplies a nonzero determinant eigenvector
over fields and a natural algebraic family of coordinate vectors. The
stabilizer of its line, its opposite-unipotent orbit and any orbit inverse,
root weight, modulus-height or analytic convergence estimate remain
separate obligations.
