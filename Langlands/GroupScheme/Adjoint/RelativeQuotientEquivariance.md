# Inner-discrepancy transport through relative full-centre quotients

This internal derived module works over any scheme. The supplied maps
`q : G ⟶ A` and `p : H ⟶ B` are fppf quotients by their full centres.
The specified actions of `A` on `G` and `B` on `H` restrict along these maps
to conjugation. For any natural local isomorphism `e : LocalGroupIso G H U`,
the induced quotient family `hq.localIso hp e` is equivariant for these actions.
The definition `hq.equivariantLocalIso hp a b ha hb e` packages this induced
family together with its equivariance proof as a subtype.

The proof pulls back the fppf map `q` along the acting point. On that test,
the acting point lifts to a group point, so the specified action is
conjugation. The quotient square and multiplicativity of the local
isomorphism identify the two conjugation formulas. Epimorphy of the
pullback map descends the equality to the original test scheme.

The inverse, composite, and common-source comparison families therefore
have inner discrepancy whenever the original families do. The last two
lemmas apply the same constructions after refining distinct covers to
their fibre product. These consequences use the previously constructed
all-refinement discrepancy formulas in `InnerDiscrepancySymmetry` and
`InnerDiscrepancyComposition`; equivariance is discharged by the construction
here, rather than added as a premise.

This module assembles the existing full-centre quotient and fppf lifting
interfaces. It requires no quasi-compactness or field assumption. It
asserts no existence of full-centre quotient data and no quasi-split
existence or uniqueness theorem.
