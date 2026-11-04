# Contraction and positive weights for a split dynamic centralizer

This is an internal consequence of the published scheme-level limit map,
vanishing of homomorphisms from unipotent groups to split tori, and actual
Lie-weight decomposition. It introduces no new literature assertion.

Work over any field in universe `u`. Let `χ : Gm → G` be a cocharacter
of a separated group scheme. Supply actual representatives `p : P → G`
of `Dynamic.parabolic χ` and `z : Z → G` of `Dynamic.centralizer χ`.
Assume `Z` is a split torus. For any unipotent group scheme `H` and
homomorphism `i : H → G` whose whole-test range is contained in
`Dynamic.parabolic χ`,
`Dynamic.range_le_unipotent_of_splitCentralizer` proves that its whole-test
range is contained in `Dynamic.unipotent χ`.

The proof factors `i` through `P`, then composes with the actual limit
homomorphism `P → Z`. The published
`IsUnipotent.comp_eq_one_of_isSplitTorus` makes every point of this
composite equal to the identity.
The all-test evaluation formula for the limit homomorphism shows that
every image point has identity limit, on its original test scheme.
No closedness, smoothness, connectedness, or normalization of `i` is
required. Supplying an actual representative `u : U → G` of the dynamic
unipotent functor gives the homomorphism
`Dynamic.unipotentFactorOfSplitCentralizer : H → U`, and its composite
with `u` is exactly the original `i`.

The weight conclusions assume that `G` is affine and locally of finite
type, and that the cocharacter factors through a supplied split
commutative torus `j : T → G` as `χ = groupHom ν ≫ j`.
For any subgroup functor `F` contained in `Dynamic.unipotent χ`,
`RelativeRoot.actionWeightSupport_subset_positive_of_le_unipotent`
places its complete ambient tangent-weight support in the
strictly positive pairing region. Zero is retained in the definition
of support and is excluded by this conclusion. The proof uses the
published identification of the tangent submodule of the dynamic
unipotent functor with the positive weight span, then the published
support bound for tangent containment. It does not assume that `F`
is represented.

For an affine source `H`, an actual action `a` of `T` on `H`, and an
equivariant monomorphism `i : H → G` into conjugation along `j`,
`AutomorphicAction.IsEquivariant.latticePairing_pos_of_range_le_unipotent`
proves strict positivity for every nonzero actual source Lie weight
space. Equivariant tangent transport identifies such source weights
with the ambient support of `range i`, so the preceding support bound
applies. The source weight spaces test all coefficient algebras.

The split-torus description of the dynamic centralizer and the
parabolic containment are explicit local inputs. This module does not
construct a Borel-defining cocharacter, prove that its centralizer is a
torus, construct root reflections, or prove the final arbitrary-field
Levi-centralizer assertion.
