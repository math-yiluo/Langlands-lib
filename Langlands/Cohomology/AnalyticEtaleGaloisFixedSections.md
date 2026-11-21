# The deck action on fixed sections of an étale G-sheaf

This internal construction works with the distinguished étale lifts and the
fixed submodule in `AnalyticEtaleGaloisCoinducedLocalAcyclic`. For an ordinary
arrow between two distinguished objects with supplied lifts, admissible
refinements give a subgroup on which the arrow intertwines the lifts. The arrow's
trivial twist forces the two group elements furnished by restriction
equivariance to agree. A finite intersection makes a supplied lift commute with
all of the deck automorphisms.

The left representation on fixed sections acts by restriction along the inverse
deck arrow. Commutation with the lift makes this restriction preserve the fixed
submodule. The contravariant sheaf maps and the inverse in the deck index give
the representation laws.

For a finite deck group in `Type`, `galoisFixedSectionRep` transports this
representation along `ULift` to the universe of the coefficient ring. On a
distinguished object, assume the deck action over the base is free on
`L`-valued points, the supplied lift commutes with the deck action, and the
subgroup defining the fixed submodule is open in `G` and contained in the lift
subgroup. Under these hypotheses, `HasCoinducedGaloisFixedSections` gives a
linear coordinate map on sections. Its restriction to the fixed submodule
supplies bijective coordinates indexed by the inverse action on the
representation, after reindexing along `ULift.down`. The coinduction
criterion in `CoinducedFilteredAcyclic` then gives vanishing of
`groupCohomology` in each positive degree.

This implements the fixed-section algebra used in step (1′) of Berkovich's
*Étale equivariant sheaves on p-adic analytic spaces*, Proposition 1.5.1,
printed p. 11, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
