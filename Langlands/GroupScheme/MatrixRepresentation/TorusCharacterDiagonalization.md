# Simultaneous torus-character diagonalization

This internal module, which supports the actual open-cell height estimate,
chooses one coordinate change diagonalizing an entire supplied split
torus. It uses the published character-space decomposition and character
basis, including their universal coefficient-algebra equations.

`HasTorusCharacterDiagonal ρ i χ` states the equality on every coefficient
algebra between the representation restricted through `i` and the
diagonal matrix of the actual algebraic characters `χ`. There are no
reducedness restrictions on those coefficient algebras.

`exists_hasTorusCharacterDiagonal` uses
`iSup_characterSpace_eq_top_of_isSplitTorus` and
`exists_characterBasis` for the restriction of the original
representation to the supplied torus. The resulting
`basisCoordinatePoint` is one rational point of the general linear
group. Conjugation by it gives the displayed diagonal equation by
`conjugate_basisCoordinatePoint_affineMatrix`.

The actual torus characters are retained.
`HasTorusCharacterDiagonal.cocharacter` proves that every cocharacter
composite in these same fixed coordinates is the diagonal cocharacter
whose exponents are the integral lattice pairings with those characters.
The proof evaluates at the universal multiplicative-group point.
Composition of an actual character with an actual cocharacter is the
integer power prescribed by `gmEndEquiv` and `latticePairing_apply`.
The universal-point extensionality theorem then gives equality of the
group-scheme morphisms themselves.

Over a nonarchimedean local field,
`HasTorusCharacterDiagonal.latticeSection` identifies the matrix of
each intrinsic uniformizer-section point with the diagonal matrix of
those pairing powers of the chosen uniformizer unit. It applies the
cocharacter equality and the published
`rationalMatrix_gmRationalPoint_comp`. There is no additional choice of
coordinates for each cocharacter.

The construction works over any field, in any characteristic. It assumes
splitness of the supplied torus, but no reductivity, maximality,
closedness of the matrix representation, or local-field topology. The
last uniformizer-section specialization explicitly requires the
nonarchimedean local-field structure used to define that section. All
field universes are arbitrary. The module is an internal consequence of
the published representation and torus interfaces, rather than a
translation of a separately named source theorem.
