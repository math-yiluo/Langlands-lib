# Geometric properties of the actual finite-cover filtration

This is an internal construction for the supplied relative radical filtration.
It applies the existing local root-weight geometry to the actual groups and
maps assembled in `FiniteFaceCoverGroups`.

The local terms are smooth and closed in the original pulled-back ambient
group. Their successive inclusions are closed, and their original projections
are full fppf quotients by the actual next terms. Smoothness of the assembled
terms and vector layers follows on the component open cover. Closedness of the
assembled ambient and successive inclusions, and flatness, surjectivity and
local finite presentation of the assembled quotient maps, follow on that same
cover. Actual component isomorphisms transport the prescribed maps, so these
properties concern the original maps, including zero-rank layers.

The full scheme-theoretic kernel of each assembled projection is exactly the
range of its actual successive inclusion on every scheme test. The proof
transports kernel ranges through the component isomorphisms, applies the local
full quotient kernel equality, and reflects equality of the two monically
represented subgroup functors on the component open cover. Consequently the
assembled map is a full fppf quotient by the next term, and that next term is
normal in the preceding term.

The morphism-property helpers use the actual pullback square of a base-changed
group homomorphism and locality on the target. All constructions and proofs
allow an arbitrary universe, disconnected coefficient rings, and empty covers.
This module is an intermediate descent input; it does not assert a filtration
over the original base.
