# Base change of fppf-local commutator membership

For an arbitrary base morphism `b : S' ⟶ S`, the actual multiplicative pullback
adjunction on points identifies `RelativeDerived.LocallyCommutator` for the
base-changed group with the same predicate for the original group on the test
scheme viewed over `S`. No flatness, finiteness, or affineness condition is
placed on the base morphism, the group, or the test scheme.
The definition `locallyCommutatorBaseChangeEquiv` restricts that equivalence
to the actual sets of points satisfying the local predicate.

The proof uses the same fppf covering family in both directions. On each cover
member, the pullback point equivalence preserves the abstract commutator
subgroup because it is a multiplicative equivalence. Identity maps of the
underlying cover schemes account for the associativity of the structure maps
to `S`. The proof is an internal formal consequence of the unchanged
`RelativeDerivedInputs` predicate and the published pullback point equivalence;
it assumes no reductive-group structure theorem or relative derived-group
existence theorem.
