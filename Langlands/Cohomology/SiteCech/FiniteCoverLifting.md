# Lifting coefficient maps over finite basis covers

This internal prerequisite works on an arbitrary Grothendieck site `(C, J)`,
with a specified family `B : ι → C`. `FiniteBasisCover J B U` stores a finite
list of indices, arrows from the corresponding `B` objects to `U`, and the
proof that these arrows generate a covering sieve. The proposition
`HasFiniteBasisCoverRefinements J B` requires that each covering sieve on
each `B i` contain such a finite cover. This is an explicit geometric
hypothesis; the module does not prove it for an analytic site.

For a commutative ring `R`, module sheafification, and local smallness in
the coefficient universe, `FiniteBasisCover.freeSource` is the finite
coproduct of free representable module sheaves on the cover domains.
`FiniteBasisCover.freeAugmentation` is the coproduct map induced by the
cover arrows to the free representable sheaf on the covered object.

`FiniteBasisCover.exists_free_lift_of_imageSieve` assumes that every
cover arrow lies in the image sieve of the section represented by a
coefficient map `s`. Choose a section preimage on each arrow, convert each
preimage into a map from its free representable sheaf, and form their
coproduct map. The two naturality laws for `freeRepresentableHomEquiv`
and the coproduct universal property prove
`t ≫ f = freeAugmentation ≫ s`. This first result does not require `f`
to be an epimorphism.

Under `J.WEqualsLocallyBijective (ModuleCat R)`, an epimorphism of module
sheaves is locally surjective, so the section's image sieve is covering.
`exists_finiteBasisCover_lift` applies the finite-refinement hypothesis
to that sieve and then the preceding assembly result.
`exists_finiteBasisCover_lift_of_shortExact` uses the epimorphic second
map of a short exact coefficient sequence.

The provenance is internal: these are consequences of the module-sheaf
adjunction, the Yoneda equivalence, local surjectivity of module-sheaf
epimorphisms, and finite coproducts. They supply the degree-zero local
lifting step needed by a finite Čech test system whose augmentation is
this map. Constructing its exact augmented complexes, finite presentations
of every higher term, and the analytic finite-refinement instance remains
separate work. No comparison or analytic acyclicity theorem is asserted.
