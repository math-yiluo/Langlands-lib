# A right adjoint for actual unnormalized parabolic induction

This module proves
`Langlands.Aubert.General.RepresentedParabolic.LeviUnnormalizedInductionRightAdjointStatement.{u,v}`
by the theorem `leviUnnormalizedInductionRightAdjoint`.

The source assertion is the first sentence of the Remark in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition of 9 July 2026,
VI.1.1, printed page 135 / PDF page 141, registered as
`renard-2026-representations-groupes-reductifs-padiques`.
The proof uses the special adjoint functor theorem, rather than constructing the
source's pseudo-forgetful right adjoint.

For a group `H : Type u`, work in smooth complex representations with carriers
in `Type (max u v)`. Two private categorical helpers assemble published results.
First, the actual smooth direct-sum cofans in `SmoothCoproducts` supply
coproducts indexed by every type in the carrier universe. The category is
abelian, so it has coequalizers, and Mathlib constructs arbitrary colimits from
these coproducts and coequalizers.

Second, index the published resized permutation representations
`Jacquet.smallFixedVectorGenerator K` by all open subgroups `K` of `H`.
Both the index type and the coset types lie in universe `u`, hence fit the
common carrier universe. Every vector of a smooth representation is fixed by
some open subgroup. The published `smallFixedVectorLift` maps the identity-coset
vector to that vector. Thus two morphisms agreeing after every map from this
family agree on every vector. This is a small separating family. Compactness of
the open subgroups is unnecessary for this argument.

For the rational Levi's smooth category, the separating family is detecting
because the category is abelian and therefore balanced. Mathlib then proves
well-poweredness from the detecting family; the abelian subobject/quotient
duality gives well-poweredness of the opposite category. Hom types of both
smooth categories fit the common universe.

The final proof introduces exactly the field, group, rational parabolic triple,
topologies and semidirect decomposition in the published target. It obtains
colimit preservation of the target's own composite from
`leviUnnormalizedFunctorsPreserveLimits.{u,max u v}`, taking its final conjunct.
The special adjoint functor theorem
`isLeftAdjoint_of_preservesColimits_of_isSeparating` now yields `Ind.IsLeftAdjoint`,
the existence of a right adjoint in the same carrier universe.

The categorical helpers are internal derived arguments from the published
direct-sum and permutation constructions and Mathlib's categorical theorems.
No hypothesis is added to the target, and no particular right-adjoint
construction or second-adjointness identification is asserted.
