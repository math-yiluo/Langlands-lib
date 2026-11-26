# Characters of the norm quotient and stabilizer divisibility

`normTrivialCharacterGroup F E` is the subgroup of complex characters of
`Fˣ` that satisfy `IsNormTrivial E`. The latter condition requires a character
to take the value one on the determinant norms of all members of `Eˣ`.
For a finite extension, `normTrivialCharacterEquiv` descends each such
character to the actual quotient `Fˣ / N(Eˣ)` and gives pullback as its inverse.

For a characteristic-zero nonarchimedean local field `F` and a cyclic field
extension `E/F` of degree `l`, `card_normTrivialCharacterGroup` gives the
cardinality `l`. The Lean proof applies
`LocalClassField.NormUnitImage.normSubgroup_index_eq_finrank` to p-adic
realizations on the original field carriers. The algebraic cyclicity data give
an abelian Galois extension, so the quotient has cardinality `l`. Complex
roots of unity and finite abelian duality give the same cardinality for its
character group. `normTwistStabilizer_card_dvd` then applies Lagrange's theorem
to the inclusion of the determinant-twist stabilizer in this group.
These two cardinality results use arbitrary field and representation carrier
universes.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.1.3 (printed p. 56,
PDF p. 64) defines the group `K(E/F)`. II.4.12, Proposition (printed p. 96,
PDF p. 104) uses its stabilizer for an irreducible cuspidal representation.
Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
