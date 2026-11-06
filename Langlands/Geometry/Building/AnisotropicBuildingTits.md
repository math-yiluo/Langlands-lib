# The actual Tits witness for an anisotropic building

This is a derived internal construction from the existing KP Tits-system,
actual building-facet, and quotient definitions. The data are supplied actual
`ParahoricBuildingData`, without changes to their quotient, action, topology,
centralizer, or valuation normalization. The construction does not establish
existence of these data for an arbitrary connected reductive group.

The group-theoretic helpers show that a full Borel subgroup, full normalizer,
trivial Weyl group, and empty simple-reflection set form a saturated Tits
system. The simple-reflection axioms have no cases. Every admissible parabolic
is the full group, and every restricted apartment is its singleton collection.

For a supplied actual reduced quotient that is a subsingleton, every building
facet is nonempty and therefore is the whole quotient. Its stabilizer in the
original `zeroSubgroup` is the whole `zeroSubgroup`. Apartment images also fill
the quotient. These facts prove all six fields of the existing
`IsBuildingTitsSystem` predicate: the Tits axioms, finiteness, saturation,
bijectivity on all facets, the opposite face-order relation, and equality of
the collections of apartments. The generic witness retains an explicit premise
that the actual normalizer is the full rational-point group.

`anisotropicTitsData` explicitly packages the trivial Weyl map together with
all six existing building-system fields for each actual apartment chamber.
Its Weyl map is the constant identity homomorphism by definition; its simple
reflection set is empty. The theorem `hasTitsSystem_of_isAnisotropic`
discharges both premises using the
published root-free quotient geometry and the theorem that split subtori in an
anisotropic group admit only one homomorphism to any group scheme. The witness
uses `PUnit` as the Weyl group in the original universe and no simple
reflections. This proves precisely the existing `HasTitsSystem` predicate
(KP Axiom 4.1.9) on the supplied actual parahoric data at every universe `u`.
General-root data, building realizations, apartment splittings, bounded open
stabilizers, and unconditional construction remain separate obligations.
