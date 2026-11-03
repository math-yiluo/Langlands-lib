# Included represented subgroups and semigroup Lie uniqueness

This internal helper constructs the actual morphism between representatives
of two subgroup functors included on every test scheme. It also reduces a
subgroup-equality step to `LieSubgroupEqualityStatement`. The original
`eq_of_le_of_hasLieImage` retains that explicit premise.
`IsSmoothConnectedClosed.eq_of_le_of_hasLieImage` now instantiates it with
the published proof `Langlands.GroupScheme.lieSubgroupEquality`, imported
from `Lie.SubgroupEqualityProof`.

`SubgroupFunctor.IsRepresentedBy.homOfLe` uses the published fully faithful
group-valued Yoneda lift, with the inclusion of the two subgroup point groups
on each test. `homOfLe_comp` and `homOfLe_comp_apply` identify its composite
with the ambient inclusion. If both representatives are closed in the
ambient group, `homOfLe_isClosedSubgroup` follows by cancelling the target
closed immersion from this composite.

`RelativeRoot.eq_of_le_of_hasLieImage` takes two smooth connected closed
subgroup functors `F` and `F'`, an all-test inclusion `F ≤ F'`, and the
assertion that both have the same actual Lie image `W`. It chooses their
closed representatives `j : H → G` and `j' : H' → G`, and applies the
preceding construction to obtain `f : H → H'`.

For an arbitrary dual-number identity-kernel point of `H'`, composition
with `j'` gives an ambient Lie vector lying in `W`. The equality of Lie
images gives a lift to an `H`-point over the same dual-number test.
Monicity of `j` shows that this lift reduces to the identity, so it is
an actual Lie point of `H`. Monicity of `j'` then shows that its image
under `f` is the original Lie point of `H'`.

The explicit premise `LieSubgroupEqualityStatement` now makes the range
of `f` all of `H'` on every scheme test. Composition with the ambient
inclusions gives `F' ≤ F`, and antisymmetry proves equality.
Affineness of `H'` is inherited from the closed immersion into affine `G`.
Smoothness and connectedness are taken from the supplied representative
witnesses; no ambient smoothness or torus action is needed.

The semigroup reductions assume an affine ambient group locally of finite
type over any field and an actual action of a split torus. Ambient
smoothness is not required here. By the published
`RelativeRoot.actionWeightSupport_subset_of_tangentSubmodule_le`
lemma from `Rational.SemigroupWeightSupport`, tangent containment in the selected
semigroup weight span implies support containment. Thus a smooth connected
stable closed subgroup with that tangent bound is an admissible generator,
so it lies in the actual generated functor on every test scheme.
`le_semigroupSubgroup_of_hasLieImage` specializes this result to the exact
Lie image. It needs no representative of the generated functor.

`semigroupSubgroup_maximality_of_hasLieImage` applies the same support
bound to the generated subgroup and then uses the published closure
maximality lemma. Exact Lie image of the generated functor suffices; this
step does not assume its smooth representability.

Finally, `eq_semigroupSubgroup_of_hasLieImage` assumes that the actual
generated functor has a smooth connected closed realization and the exact
selected Lie image. Every smooth connected stable closed subgroup with
that Lie image lies in the generated functor by the preceding generator
inclusion. Applying the proved included-subgroup equality theorem gives
equality. The smooth realization and exact Lie image of the generated
functor remain explicit geometric premises. No separate common envelope
or arbitrary comparison of subgroups from Lie images alone is asserted.

The provenance is internal: the construction and proofs use the published
Yoneda lift, actual all-test subgroup and Lie-image definitions,
closed-immersion cancellation, the full-Lie theorem, the intrinsic
split-torus support bound, and the closure universal property. This unit
does not prove smooth realization, exact Lie image, unipotence or
split unipotence of the generated semigroup subgroup, and hence does not
prove the full `SemigroupRealizationStatement`.
