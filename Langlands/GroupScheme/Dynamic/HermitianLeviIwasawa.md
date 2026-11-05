# Levi-compatible polar Iwasawa from Hermitian weight data

Author: Worker 1655.

This internal construction works over any `RCLike` field `𝕜 : Type u`.
It converts a compatible closed star-stable matrix realization with Hermitian
cocharacter weight projectors into the existing diagonal realization, and
therefore constructs all four actual-point Levi-compatible Iwasawa conclusions.
Existence of the compatible realization remains an explicit hypothesis.

`HasHermitianStarLeviRealization p m` is a Prop-valued predicate for two
specified group-scheme morphisms into the same ambient group. It supplies a
closed representation on `Fin d`, one actual cocharacter `χ`, Hermitianity of
every Laurent weight projector of `χ ≫ ρ`, representation of the dynamic
parabolic by `p` and of the dynamic centralizer by `m`, and stability under
conjugate transpose of the actual base-field matrix-point range. These are
algebraic representation and point-image conditions; they contain no compact
subgroup or Iwasawa conclusion.

The first helper computes the actual base-field affine matrix of a representation
conjugated by `baseOfMatrix g`: it is `g * ρ(x) * g⁻¹`. This follows from the
published conjugate representation formula, the standard representation formula,
and the calculation of constant points of `baseOfMatrix`. The algebra map from
the coefficient field to itself is the identity.

The next helper proves that this coordinate change preserves star stability when
`g` is unitary. For an original point `x`, choose an original point `y` whose
matrix is `star (ρ(x))`. Since `star g = g⁻¹`, the conjugated matrix of `y` is
the star of the conjugated matrix of `x`. The same actual preimage `y` witnesses
membership in the conjugated representation's range.

`HasHermitianStarLeviRealization.hasDiagonalStarLeviRealization` applies unitary
cocharacter diagonalization to `χ ≫ ρ`. Conjugate the ambient representation
by the resulting unitary base matrix. Composition with the inner scheme
automorphism preserves closed immersion. Associativity and the diagonalization
identity give literal compatibility with the diagonal cocharacter. The dynamic
parabolic and centralizer in the original ambient group retain their same
representatives, and the helper supplies star stability of the new matrix range.
These are exactly the existing `HasDiagonalStarLeviRealization` data.

When the ambient scheme is affine,
`HasHermitianStarLeviRealization.hasLeviCompatibleDecomposition` invokes the
published diagonal polar construction. Its compact subgroup is the unitary
inverse image for the conjugated representation. It has unrestricted ambient
maximal compactness, ordered parabolic-range-times-compact coverage, literal
parabolic/Levi intersection equality, and maximal compactness of its comap on
the actual specified Levi point carrier. The point groups use their own
regular-function evaluation topologies, installed explicitly in this module.

The provenance is internal composition of the matrix conjugation, unitary
weight diagonalization and diagonal polar constructions. This module does not
prove that the rational pair in the full
`InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement` admits such Hermitian
realization data. The host existence target retains that obligation.
