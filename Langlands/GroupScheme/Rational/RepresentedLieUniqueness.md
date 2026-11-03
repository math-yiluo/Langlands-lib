# Included represented subgroups with the same Lie image

This internal helper constructs the actual morphism between representatives
of two subgroup functors included on every test scheme. It also reduces a
subgroup-equality step to the existing `LieSubgroupEqualityStatement`, which
remains an explicit proof premise.

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

The provenance is internal: the construction and proof use the existing
Yoneda lift, all-test subgroup and Lie-image definitions, elementary
closed-immersion cancellation, and the explicitly assumed published
proposition. The unit supplies no proof of that proposition and no
unconditional uniqueness theorem for semigroup subgroups. Its role is to
make the remaining geometric input to the semigroup uniqueness argument
precise.
