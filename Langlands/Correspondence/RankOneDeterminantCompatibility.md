# Determinant and central action for the actual rank-one correspondence

This internal derivation proves determinant and central-character compatibility
for the actual rank-one bijection `rankOneReciprocityEquiv`, along an explicitly
supplied reciprocity candidate. The field, Weil-carrier and automorphic-carrier
universes remain independent.

For an actual automorphic class satisfying `IsRankOneCharacter`, the proof uses
the representative and scalar-model intertwining equivalence supplied by that
relation. Surjectivity of the equivalence and its equivariance transfer the scalar
action to every vector of the representative. The determinant of the scalar
matrix in GL₁ is its original field unit. Thus `IsRankOneCharacter.centralActsBy`
proves the existing `CentralActsBy` relation at every field unit, with the
original field character as the scalar.

For an actual Weil class satisfying `IsRankOneWeilCharacter`, the determinant
descends through its representative class. The published
`FiniteRepresentation.determinantCharacter_eq` transports it across the supplied
intertwining equivalence. The determinant of scalar multiplication on the complex
line is the scalar itself. This proves
`IsRankOneWeilCharacter.determinant_eq` for the existing quotient-level
`irreducibleWeilDeterminant`.

Inverting the existing field-character/supercuspidal-class equivalence defines
`rankOneSupercuspidalCentralCharacter` on every actual supercuspidal GL₁ class.
The inverse identity proves its scalar-model specification, and the first result
proves that it gives the actual central action at every field unit. The output
is a continuous field quasicharacter, without a chosen reciprocity candidate.

Every rank-one Weil class is the pullback of a continuous field character along
the supplied candidate. The actual rank-one bijection realizes the same field
character on its supercuspidal image. Applying the two preceding results and
the definition of character pullback proves `rankOneReciprocityEquiv_central`:
the scalar matrix at the reciprocity image of a Weil element acts on the image
class by the determinant of the original Weil class at that element.

Finally, the proved characterization of `SupercuspidalRankOneCompatibility`
identifies the rank-one component of any such family with this bijection.
Rewriting by that equality proves
`SupercuspidalRankOneCompatibility.determinant_rankOne`. This is precisely the
rank-one specialization of `SupercuspidalDeterminantCompatibility`.

The source is internal linear algebra and transport through the existing actual
class relations. No reciprocity candidate is constructed, and no geometric
normalization premise is needed for these implications. No higher-rank
determinant compatibility, twist or dual compatibility, pair factor
compatibility, or closed correspondence theorem is asserted here.
