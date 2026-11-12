# Invariant subspaces across independent carrier universes

This internal algebraic helper uses actual intertwiners, invariant subspaces
and representation equivalences with independent carrier universes.

`intertwinerPreimage` is the submodule inverse image with its invariance
certificate. `intertwinerPreimageMap` is the actual restricted intertwiner
into the chosen target subspace. An injective original map restricts to an
injective map. `iSup_intertwinerPreimage_eq_top_of_equiv` uses the submodule
order isomorphism induced by an actual representation equivalence to pull
a spanning invariant family back to a spanning family in the original
carrier, with no restriction on the index universe.

`intertwinerImageEquiv` restricts an injective intertwiner to its actual
invariant image. Its range restriction is bijective and hence is an actual
representation equivalence, including across carrier universes.

`IsSubquotient.universeLift_of_injectiveIntertwiner` starts with the published
injective/surjective presentation of a subquotient in the source universe.
It lifts the intermediate smooth object, composes its injection with the
given injection, and composes its quotient map with the target constituent's
actual universe-lift equivalence. These maps are injective and surjective
respectively, so the lifted constituent is an actual subquotient of the
larger target.

These constructions are derived from the published smooth subquotient
interfaces, actual carrier lifts, and Mathlib's submodule order isomorphism.
They assert no representation-theoretic decomposition or support theorem.
