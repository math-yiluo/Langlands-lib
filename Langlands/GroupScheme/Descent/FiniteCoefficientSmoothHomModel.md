# Smooth affine simultaneous homomorphism models

This is an internal refinement of the published finite coefficient group and
homomorphism models, needed in the noetherian approximation of a supplied
locally quasi-finite flat surjective homomorphism of reductive groups.
It records the smooth affine target needed to apply eventual reductivity to
both groups. Its existence theorem takes the published proposition
`HomGeneralStatement` as an explicit premise; it does not prove that premise
or assert noetherian model existence.

`SmoothAffineHomModel` extends `SimultaneousHomModel` with an affine and a
smooth structure morphism for the target. Thus it retains the finitely
generated coefficient subalgebra, the two actual model groups, their supplied
homomorphism, two base change isomorphisms, and the exact recovery square.
Its `enlargeTo` construction reuses the published enlargement along an actual
subalgebra inclusion. Affineness and smoothness of the target survive that
base change.

`exists_smoothAffineHomModel` first models the source over finitely generated
coefficients containing the prescribed finite subset. It models the target
over a finitely generated subalgebra relative to those coefficients and base
changes the source to the same ring. The explicit homomorphism descent premise
then descends the supplied map, conjugated by these two group isomorphisms.
Finite type transitivity gives finite generation over the original coefficient
ring, and the nested inclusions retain the prescribed finite subset.
The canonical direct/iterated pullback comparisons transport both isomorphisms;
cancelling the target comparison and using the premise's recovery equation
proves the required equality of actual homomorphisms.

The provenance is the existing Library constructions `exists_groupModel`,
`SimultaneousHomModel.enlargeTo`, and the explicit `HomGeneralStatement`.
No original-literature theorem is claimed for this auxiliary refinement.
