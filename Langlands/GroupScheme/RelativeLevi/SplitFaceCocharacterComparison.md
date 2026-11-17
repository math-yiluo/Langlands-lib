# Canonical face terms for different dynamic presentations

This derived unit removes the original-coordinate-cocharacter choice from
all actual face-filtration terms for a fixed ambient coordinate torus and
fibrewise root datum over a nontrivial commutative ring.

The root-sign detection theorem identifies the positive root pairings for two
equal actual contracting functors. Applying it also to opposite root labels
identifies their zero-root faces. `SplitParabolicFaceChart.reparameterize`
therefore reinterprets one actual face chart for the other cocharacter while
retaining exactly its regular chart, root labels, unscaled natural weights
and ambient maps. The perfect root-datum pairing supplies the new coweight;
equality of its simple-root zero set preserves the exact face-height formula.
Sign agreement transfers dominance, and equality of contracting functors
transfers the proved all-test representation.

The existing arbitrary-base, fixed-torus comparison now applies to this
reparameterized chart. `range_inclusion_comp_sameContracting` identifies every
actual ambient term range on all scheme tests. `sameContractingTermIso` and
its ambient equation give the corresponding actual term isomorphisms. The
two original cocharacters may have different nonzero root-pairing values.

`RelativeLevi.unipotent_eq_of_same_relativeRadical` supplies the contracting
functor equality from two dynamic presentations of the same prescribed
parabolic inclusion and the same supplied relative unipotent radical. The
published dynamic-radical theorem says that the composite radical inclusion
represents both contracting functors on all tests.
`sameRelativeRadicalTermIso` applies the comparison to these actual data and
retains the exact ambient maps. No filtration equality is supplied as a premise.

Provenance is actual split-root sign detection, the unscaled integral
face-height formula, the proved fixed-torus comparison, and the published
supplied-radical dynamic identification. Comparing different maximal tori,
changing the root-datum realization, and effective global descent remain
outside this unit's assertions.
