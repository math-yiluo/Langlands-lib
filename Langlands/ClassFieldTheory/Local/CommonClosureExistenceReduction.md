# Common-closure existence reduced to the finite cup comparison

This internal reduction keeps `FiniteCupArtinCharacterComparison` as an
explicit mathematical premise. It is not an unconditional proof of the
host task's common-closure reciprocity existence target.

The finite Galois restriction comparisons identify the constructed
family's values with geometric abelianized finite Artin symbols. The
finite transfer theorem, conditional on the comparison, supplies the
transfer square at every finite Galois overfield. Cofinality and separation
of these restrictions then give the actual fixing-subgroup Galois transfer
square. The proved Galois-to-Weil comparison gives the actual Weil
transfer law.

`constructedReciprocityFamily_galoisTransfer` performs this finite test for
every pair of finite intermediate fields, including nonnormal ones. The
top finite field is Galois over the original base and therefore normal
over both intermediate fields; all inclusion algebras and scalar towers
are those of the literal fields. The transfer maps on both sides are the
existing finite-coset products, related by the proved finite restriction
square.

`constructedReciprocityFamily_normalized` combines this transfer law with
the already proved norm, conjugation, density, actual multiplicative
completion and absolute-value normalization laws.
`normalizedSystemOfFiniteComparison` packages the same constructed family
with those laws.

The final theorem
`commonClosureReciprocityExistence_of_finiteCupComparison` has conclusion
exactly `CommonClosureReciprocityExistence.{u}`. It preserves the target's
prime, arbitrary field universe, supplied base topological datum, actual
canonical extension topologies, and all intermediate fields. Its finite
character comparison hypothesis remains explicit. Removing that
hypothesis requires an independent proof of the exact finite comparison;
the present reduction does not provide one.
