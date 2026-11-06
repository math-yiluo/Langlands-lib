# The actual regular action on the full binary covariant space

Let `k : Type u` be a field and `m` a natural number. Use the actual upper
triangular subgroup of the binary special-linear group scheme and its
last-diagonal character. The basis `covariantBasis m` transports the full binary
monomial basis through `covariantRowEquiv m` onto the entire actual affine
coordinate subspace with left weight `characterCoordinate k ^ m`.
The matrix representation `covariantRegularRepresentation m` is the existing
Chevalley finite regular representation constructed in this basis. Its stability
proof is the general right-translation stability of left covariance.

The affine matrix of this representation at the point classified by
`g : SL(2,k)` equals `binaryMatrixRepresentation m g`, the homogeneous
polynomial substitution matrix. To prove this, `matrixPoint_map` identifies
base extension of a classified affine point, and naturality gives the same
base-extension identity for the regular matrix. Evaluate the general regular
basis multiplication identity on `Spec C`, where `C` is the determinant-one
coordinate ring, at the universal matrix and the scalar extension of `g`.
The actual affine evaluation formula identifies the resulting equation with
right translation of a bottom-row monomial, after applying the inverse affine
sections equivalence. Its injectivity gives
`rightTranslation_binaryBasis`. The existing homogeneous-row intertwining
identity and injectivity of the bottom-row map then give the action on each
homogeneous basis vector. Extracting basis coefficients proves
`covariantRegularRepresentation_affineMatrix`.

The multiplicative equivalence `rationalPointsEquiv` identifies the actual
scheme's rational points with determinant-one matrices over `k`, using the
affine point equivalence and the base affine test isomorphism.
`covariantRegularRepresentation_rationalMatrix` applies the general comparison
between rational and affine matrices. Consequently the actual rational-point
representation equals `binaryRepresentation m` pulled back through
`rationalPointsEquiv`.

For a prime `p`, an infinite field `k` of characteristic `p`, and every natural
`s`, `covariantRegularRepresentation_isIrreducible` proves irreducibility at
`m = p^s - 1`. It uses the already proved binary polynomial irreducibility and
the general invariance of irreducibility under pullback by a group equivalence
from `CuspidalSupport.AssociationReduction`. This is irreducibility of the
actual finite regular representation in a basis of the entire covariant
subspace. The comparison statements hold over every field and degree, while
the irreducibility theorem retains the explicit infinitude premise.

This derived unit uses the existing actual subgroup, full covariant-space
equivalence, homogeneous action, finite regular representation and generic
pullback constructions. It assumes no Steinberg irreducibility or structural
group-theory assertion beyond these proved Library results. It does not
identify the character with negative rho, establish Borel status, or prove the
general `SteinbergBigCellStatement`.
