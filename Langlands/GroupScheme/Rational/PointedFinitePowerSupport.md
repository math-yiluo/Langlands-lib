# Actual pointed finite powers and augmentation support

This internal construction equips the existing `GroupScheme.finitePower V n`
with the diagonal action and the tuple of distinguished fixed points. Its
action morphism is exactly the one supplied by `PointwiseSchemeAction.finitePower`;
forgetting the distinguished point recovers that action.

`finitePowerZeroIso` identifies the empty power with the terminal scheme over
the base. `finitePowerSuccIso` separates coordinate zero from the coordinates
indexed by successors. The two maps are inverse by their projections. These
isomorphisms also show that finite powers of an affine scheme over the field
have affine structure morphisms.

The successor isomorphism preserves the distinguished point and is equivariant
on every test scheme, as is checked on each coordinate projection. For the empty
power every test point is equal to its distinguished point. Evaluating an
augmentation coordinate at the universal point therefore makes that coordinate
zero. Its augmentation support is empty.

`finitePower_support_subset_semigroup_of_split` states that, for an actual split
torus over any field, every finite power has augmentation support in any additive
subsemigroup containing the original augmentation support. The proof uses the
empty-power calculation for zero and the existing binary product-support bound,
transported across the pointed equivariant successor isomorphism, for induction.
The semigroup is arbitrary and need not contain zero; zero is never inserted.
The universe and the all-coefficient-algebra eigenconditions are unchanged.

This is a derived extension of the identity-slice product argument motivated by
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), Lemma 3.3.4,
printed pp. 108–109 (PDF pp. 134–135). It uses the existing product-support and
split-torus decomposition results. It does not establish generated-envelope
geometry or the host `SemigroupCommutatorStatement`.
