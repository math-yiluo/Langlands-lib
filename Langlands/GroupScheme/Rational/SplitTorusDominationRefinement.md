# Scalar extension and normal-closure refinement of split torus domination

This internal construction extends an actual pointed dominant morphism from
a split torus along field extensions. It also enlarges a finite separable
field of such domination to a finite Galois one. It preserves the original
group as the target before scalar extension. All fields lie in the same
arbitrary universe `u`; there is no characteristic, cardinality or perfection
restriction. These parametrizations are scheme morphisms and need not be
group homomorphisms.

`HasPointedSplitTorusDomination.of_iso` composes the supplied parametrization
with the underlying scheme isomorphism of the target group. Dominance is
preserved by composition with that isomorphism. The group-scheme
isomorphism preserves identity, so the parametrization stays pointed. This
transport requires no geometric assumptions on the target.

`HasPointedSplitTorusDomination.baseChange_of_isReduced` assumes the target
is reduced and affine. It pulls back the actual parametrization. The split
torus remains split. Existing dominance transport uses that the source
torus and target are affine, the parametrization is quasi-compact and
schematically dominant, and field extensions are flat. The existing
pullback identity equation retains pointedness. Thus ordinary dominance is
not being asserted to survive arbitrary base change without hypotheses.

`HasPointedSplitTorusDomination.baseChange` assumes instead that the target
is smooth and affine. Its supplied pointed torus domination forces
connectedness. Existing smooth connected affine geometry makes the target
geometrically integral, hence reduced, and the preceding result applies.
This works for inseparable and transcendental field extensions as well.

`HasPointedSplitTorusDomination.baseChange_fieldTower` pulls the middle-field
parametrization back to the last field of any compatible field tower.
Smoothness and affineness hold for the middle-field target by pullback. The
inverse direct-versus-iterated `baseChangeFieldTowerIso` then transports the
parametrization to the direct scalar extension of the same original group.

`HasPointedSplitTorusDomination.exists_finiteGalois_of_finiteSeparable`
embeds the supplied finite separable field into a separable closure of the
ground field and takes its normal closure there. Existing field-theory
instances make the result finite Galois and give the compatible algebra
tower. The preceding lemma extends the supplied split-torus domination to
the direct scalar extension of the original group to this field. No
split-unipotence conclusion is asserted.

`HasPointedSplitTorusDomination.finiteGaloisRefinement` chooses the resulting
field and parametrization in the existing
`FiniteGaloisSplitTorusDomination` structure. It retains the field and its
finite-Galois instances, actual split torus, actual scheme morphism,
dominance and pointedness. It does not retain a specified embedding of the
initial field or assert equality with a specified initial parametrization.

The provenance is internal composition of pointed torus-domination
base change, split-torus base change, isomorphism transport, the existing
direct/iterated group-scheme pullback comparison, and the field-theoretic
normal-closure construction. The splitness criterion for unipotent targets
and the rational maximal-torus conjugacy theorem remain separate proof
obligations.
