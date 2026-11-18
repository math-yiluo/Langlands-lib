# Unipotent groups and groups of multiplicative type

`Langlands.GroupScheme.unipotentMultiplicativeTriviality` proves the published
[`UnipotentMultiplicativeTrivialityStatement`](MultiplicativeTrivialityStatement.md)
in every universe. The statement is the conjunction of Milne 14.16, 14.17,
and 14.18.

For a homomorphism from a group of multiplicative type to an affine unipotent
group, the proof uses `IsMultiplicativeType.hom_eq_zero_of_isUnipotent` from
[`MultiplicativeTypeUnipotentHom`](../Torus/MultiplicativeTypeUnipotentHom.md).
That theorem follows from the diagonalizable-source Hopf-algebra argument
and faithful pullback to a splitting field. Applying it to the identity
proves triviality when a group has both properties.

For the intersection of `i : U ⟶ G` and `j : M ⟶ G`, the proof takes their
group-scheme pullback using
[`SubgroupIntersection`](../SubgroupIntersection.md). The projection to `M`
is a base change of the closed immersion `i`. Hence the pullback is of
multiplicative type by `IsMultiplicativeType.of_isClosedSubgroup`. Since
`U` is affine by composition of its closed immersion and the affine
structure map of `G`, the projection to `U` is zero. The composite into `G`
is zero as well, and its range is the intersection of the two ranges on
every test scheme.

For a homomorphism from `U` to `M`, the proof uses the splitting extension
given by `IsMultiplicativeType M`. The affine group `U` remains unipotent
after field extension. The pullback of each coordinate character on the
diagonalizable target is trivial by `IsUnipotent.characterEval_eq_one` from
[`CharacterLine`](../Rational/CharacterLine.md). The character evaluation
formula in
[`DiagonalizableCharacterProof`](../Torus/DiagonalizableCharacterProof.md)
then shows that the image of every test-scheme point has all coordinates
equal to one. The character description of points detects the identity, so
the homomorphism after base change is zero. Faithfulness of field-extension
pullback reflects this equality to the original field.
`SubgroupFunctor.range_zero` gives the claimed ranges.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), Proposition 14.16 and
Corollaries 14.17–14.18, printed p. 284 (PDF p. 300). The literature ID is
`milne-2017-algebraic-groups` and the SHA-256 is
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
