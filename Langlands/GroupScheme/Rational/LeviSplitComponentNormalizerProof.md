# Rational normalizers of a Levi and its split component

Module `Langlands.GroupScheme.Rational.LeviSplitComponentNormalizerProof`.
Namespace `Langlands.GroupScheme`.

The theorem `leviSplitComponentNormalizer` has exactly the type
`LeviSplitComponentNormalizerStatement.{u}`. For every field `k : Type u`,
connected reductive group scheme `G/k`, rational parabolic `j : P ⟶ G`,
rational Levi factor `l : L ⟶ P`, and split component `a : A.toGrp ⟶ L`,
it identifies the rational-point carriers of the normalizers of `a ≫ l ≫ j`
and of the subgroup functor `SubgroupFunctor.range (l ≫ j)`.
The normalizer conditions still test conjugation after every refinement.
The conclusion is the equality of their carriers over `Spec k`; it does not
assert equality of the whole normalizer subgroup functors.

## Source and provenance

The target is the recalled equality in Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, V.3.5.1,
printed p.110 / PDF p.116, together with the rational-point conventions on
printed p.109 / PDF p.115 and the Levi description in V.3.1 on
printed p.110 / PDF p.116. PDF pp.115–117 were read.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`.
The existing target's
[statement account](LeviSplitComponentRecallStatements.md)
records the source passage and its arbitrary-field scope.
This proof composes published Library results and the subgroup-functor laws;
it is an internal derivation of that exact target.

## Implemented proof

The rational Levi is affine because it is connected reductive.
`IsSplitComponent.torusCentralizer_comp_eq_of_parabolicDynamic`, applied to
the published theorem `parabolicDynamic`, identifies the centralizer of the
supplied embedded split component with the range of the supplied embedded
Levi. This application retains the original maps and requires no choice of
a different Levi.

For the forward inclusion,
`torusCentralizer_isNormalizedBy_torusNormalizer` says that a normalizer
point conjugates centralizer points into the centralizer on every test
scheme. Restrict the rational normalizer point to each refinement and
apply that fact both to it and to its inverse. Rewriting the centralizer
as the Levi range gives precisely the two conjugation conditions defining
the normalizer of the Levi range.

For the reverse inclusion, the composite Levi inclusion is a closed
immersion and hence a monomorphism.
`SubgroupFunctor.normalizerRestrictionIso` restricts a rational point
normalizing that range to an actual `k`-automorphism of `L`;
`normalizerRestrictionIso_hom_comp` identifies its composite with the
original inclusion with ambient inner conjugation.
`IsSplitComponent.isNormalizingPoint_of_normalizes` restricts that
automorphism to the supplied split component, using its maximal central
split-torus property. Finally `normalizerPoints_le_torusNormalizer`
turns this actual split-component automorphism into the required
all-refinements normalizer membership.

The proof keeps the universe parameter `u` and adds no field, local-field,
splitting, characteristic, or topological hypothesis. The source of the
reused automorphism lemmas is
[LeviNormalizerBridge](../../Representation/Exponents/LeviNormalizerBridge.md);
only their algebraic sections are used.
