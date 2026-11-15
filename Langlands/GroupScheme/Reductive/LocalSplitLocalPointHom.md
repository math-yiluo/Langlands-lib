# Matching point homomorphisms over local coefficient rings

This internal derived module works with actual points of reductive group
schemes over an arbitrary commutative base ring. Its test ring is any local
ring with separably closed residue field, with an arbitrary morphism to the
base. Neither ring is assumed reduced.

`LocalSplitLocalPointHomStatement.{u}` states that any homomorphism between
the actual test-point groups of two reductive groups is bijective and uniquely
determined if it matches their common torus and additive-group
parametrizations, and the associated coordinate cells are open immersions.
The base ring is arbitrary; its test ring has separably closed residue field.
The module proves this proposition at full universe. No naturality is assumed.

The implemented factorization writes every such test point as `cell(x)⁻¹ *
cell(y)` for two points of a supplied open coordinate cell. In the residue
fibre, intersect the cell open with its inverse. The existing irreducibility
and rational-density argument gives a rational point in that symmetric open
whose inverse times the given point is also in it. Taking the inverse gives a
point `q` such that both `q` and `q * g` lie in the original cell open.

The coordinate cell is a product of additive groups and a split torus.
Global functions and units lift through the residue quotient of the local
test ring, so the first coordinate point lifts. Its product with `g` has
closed point in the cell and hence factors through the open cell: every
point of the local spectrum specializes to its closed point. The resulting
identity is the stated quotient factorization. This works for every morphism
`Spec A → Spec R`, including those that do not define local homomorphisms.

For injectivity, factor a kernel element as `cell(x)⁻¹ * cell(y)`. Matching
the cells gives equality of the two target cell images. Its open immersion
is a monomorphism, so `x = y` and the original element is the identity.
For surjectivity, factor a target point in the same way and use the
corresponding quotient of source cell points. Finally, two homomorphisms
agreeing on the cell agree on every quotient of cell points, proving
uniqueness. The published formula `map_comp_cellMap` converts torus and
root matching into cell matching.

The provenance is the published local-generation coordinate-lifting argument,
its separably closed field open-intersection lemma, and the elementary
specialization argument above, followed by these elementary group arguments.
The supplied additive-group families need not carry additional root data for
this criterion: their open-cell hypotheses suffice. This module constructs
no matching homomorphism between the two groups and does not prove the
unrestricted local split Isomorphism Theorem.
