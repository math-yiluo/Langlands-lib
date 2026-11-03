# Ambient central characters of actual normalized induction

This internal construction concerns an actual semidirect decomposition
`P = M ⋉ U` in a locally compact nonarchimedean group. The radical `U` is
closed, and the full abstract ambient center is assumed contained in `M`.
The representation carrier and ambient group universes are independent.

`ambientCenterToLeviCenter` sends each ambient central element to that same
element in the full center of `M`. This is a continuous group homomorphism
for the inherited subgroup topologies. Composing a scalar central character
of the inducing representation with this map gives
`normalizedInductionCentralCharacter`, whose kernel is open whenever the
original character's kernel is open.

Conjugation by an ambient central element is the identity on `U`. Its Haar
modulus and positive half modulus are therefore one. For an actual normalized
induced function, right translation by that element can be moved to the left
by centrality. The covariance identity and the actual Levi projection then
show that the scalar action is exactly the inherited central character.
`normalizedInductionCentralCharacter_acts` records this equality on the
whole actual smooth induced representation.

`normalizedInductionUnitaryCentralCharacter` constructs the existing
`UnitaryCentralCharacter` datum for actual normalized induction from such a
datum for the inducing representation. Its scalar character is the displayed
restriction and its norm-one law is inherited.

These constructions are derived from the existing subgroup, Haar-modulus,
normalized induced-function and central-character definitions. They assert
no rational-point center comparison, compactness, unitarizability of the
whole representation, Jacquet criterion or Levi self-association theorem.
