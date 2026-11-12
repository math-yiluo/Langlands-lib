# Common-closure existence from geometric finite cup comparison

This internal reduction derives the unchanged
`CommonClosureReciprocityExistence.{u}` target from the explicit premise
`FiniteGeometricCupArtinCharacterComparison.{u}`. It makes no unconditional
claim about that premise or the host target.

The existing common-closure candidate family is constructed without a
finite cup comparison. Its finite Galois restrictions equal the geometric
abelianized carry symbols. The published arithmetic comparison reduction
in `CommonClosureExistenceReduction` was conditional on a different
finite comparison premise. This module supplies the corresponding
assembly using geometric inverse cup and the positive carry symbol.
It leaves the earlier conditional result and all underlying conventions
unchanged.

`constructedReciprocityFamily_galoisTransfer_of_geometricComparison`
tests the desired transfer identity at every finite Galois overfield of
the original base. Each such overfield is Galois over both intermediate
fields, even when those fields are nonnormal over the original base.
The existing finite restriction/transfer square identifies the
finite image of the actual fixing-subgroup transfer. The constructed
family's finite restriction formula reduces the square to
`geometricTransfer_of_geometricCupComparison`, under the stated
comparison premise. Cofinal finite restriction separation then proves
the actual fixing-subgroup Galois transfer identity.

`constructedReciprocityFamily_transfer_of_geometricComparison` applies
the established equivalence of the Galois and Weil transfer laws.
`constructedReciprocityFamily_normalized_of_geometricComparison` combines
that law with the already proved norm, conjugation, density, multiplicative
completion and absolute-value normalization laws for the same family.
`normalizedSystemOfGeometricComparison` packages that family with all
the normalized system laws.

Finally,
`commonClosureReciprocityExistence_of_finiteGeometricCupComparison`
introduces the full target telescope and uses this package. Its conclusion
is exactly the published existence proposition, for every prime and
arbitrary p-adic field universe, every supplied base topological datum,
the actual canonical topologies of extension fields, and all finite
intermediate fields. Its only additional premise is the explicitly stated
geometric finite comparison. This premise must be proved before the
theorem yields an unconditional proof.

The provenance is internal: the proof combines the existing actual-object
transport results, finite Artin transfer adapter, and five unconditional
system laws. It adds no arithmetic or cohomological assumption beyond
the displayed comparison premise.
