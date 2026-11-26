# Integral Weyl representatives and standard parabolic factorization for `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearIntegralParabolics`
proves `GeneralLinearIntegralParabolicsStatement`, the specialization of
Renard V.5.1(2)–(3) to the standard integral subgroup of `GL_N` over a
nonarchimedean local field, for every matrix size and every generic
cocharacter of the diagonal torus.
[Statement and source](GeneralLinearIntegralParabolicsStatement.md)

## Weyl representatives

Each actual normalizer class acts on the diagonal torus's character
lattice as a coordinate permutation `σ`
(`GeneralLinear.exists_permutationAction_eq_weylAction`). The permutation
matrix `GeneralLinear.permNormalizer F σ` has that same action
(`GeneralLinear.weylAction_permNormalizer`), so faithfulness of the
relative Weyl action on the character lattice of a split torus
(`IsSplitTorus.relativeWeylLatticeAction_injective`) identifies the two
classes. The permutation matrix is the image of the permutation matrix
over the valuation ring, so it lies in the standard integral-point image
(`GeneralLinear.mem_standardIntegralModel_integralPoints_iff`).
[General linear Weyl action](../../GroupScheme/Rational/GeneralLinearProof.md)
[Faithfulness](../../GroupScheme/Rational/RelativeWeylFaithfulness.md)
[Standard integral points](../../GroupScheme/IntegralModel/GeneralLinearStandardPoints.md)

## Maximal compactness in each standard Levi

Fix a set `J` of simple relative roots. Since `GL_N` is connected
reductive and the diagonal torus is maximal split, `standardCocharacter`
gives a cocharacter `ζ` of the torus whose dynamic centralizer is
represented by the literal standard Levi inclusion `Standard.leviHom`.
The weights of `ζ` define a diagonal cocharacter `χ` of the standard
integral model over the valuation ring, whose generic fibre is `ζ`
followed by the torus inclusion. The construction
`IntegralModel.DynamicCentralizer.model` gives an integral model `Z` of
the Levi, and its closed inclusion into the standard model identifies the
integral-point image of `Z` with the preimage of the ambient integral
points under the Levi inclusion.

The Levi is connected reductive as a dynamic centralizer in a connected
reductive group (`dynamicCentralizerReductive`). The special fibre of the
standard model is `GL_N` over the residue field, which is connected
reductive. Taking centralizers commutes with base change of the
cocharacter, so the special fibre of `Z` is a dynamic centralizer in that
group and is also connected reductive. The integral-model theorem
`IntegralModel.maximalCompactStatement` then shows that the integral
points of `Z` are compact and maximal among compact subgroups, and
`IntegralModel.isOpen_integralPoints_localField` shows they are open.
[Integral centralizer model](../../GroupScheme/IntegralModel/DynamicCentralizer.md)
[Maximal compactness](../../GroupScheme/IntegralModel/MaximalCompact.md)

## Parabolic factorization

The standard integral points are compact
(`IntegralModel.isCompact_integralPoints_localField`). With the
maximality just shown for every standard Levi, the theorem
`hasParabolicFactorization_of_maximal_compact_levis` gives the ordered
product of the integral Levi and unipotent intersections for every
standard parabolic.
[Parabolic factorization](ParabolicCompactFactorization.md)
