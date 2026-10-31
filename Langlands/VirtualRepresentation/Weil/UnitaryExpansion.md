# Canonical effective unitary expansions

Author: Worker 24.

This derived construction turns the published existence theorem into a canonical
nonnegative integral expansion of every actual continuous finite-dimensional
unitary complex representation. It uses the existing Jordan–Hölder coefficient
map, with no additional choice of a composition series or expansion witness in
this module.

For an arbitrary group `G : Type uG` with `[Group G]` and `[TopologicalSpace G]`,
`unitaryExactCoefficients G` is the integer linear composite of
`exactCoefficients G` and `restrictUnitary G`. It extracts only the coefficients
on the genuine continuous unitary irreducible basis. The representation carrier
universe `uV` is independent of `uG`. A topological group structure is not needed.
For an arbitrary exact virtual class this projection can discard nonunitary
coefficients; recovery of the whole class is proved for the specified unitary
objects below.

`restrictUnitary_includeUnitary` uses Mathlib's injective-domain coefficient
formula: extraction after subtype inclusion is the identity.
`unitaryExactCoefficients_realizeExact_includeUnitary` combines it with the
published left inverse `exactCoefficients_realizeExact`. These identities prove
injectivity of both `includeUnitary` and the composite of inclusion and exact
realization. `unitaryExactCoefficients_eq_of_expansion` then shows that any full
unitary-lattice expansion of an exact class equals its canonical coefficients.
This conclusion also applies to signed expansions.

`unitaryExactCoefficients_ofRepresentation_mem_effective` applies the proved
`effectiveUnitaryExactExpansion` to an actual representation `A`, its continuity
proof and its invariant positive Hermitian form predicate. The existence
witness agrees with the canonical coefficients by the preceding identity, so
those coefficients are nonnegative.

`effectiveUnitaryExpansion A hc hu` returns an element of the existing additive
submonoid `effective` on `UnitaryLattice G`, retaining its nonnegativity proof.
`effectiveUnitaryExpansion_spec` proves that inclusion and canonical exact
realization give the entire original class
`ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩`. No selected constituent or
split Grothendieck group replaces this class. Its degree theorem applies the
published exact degree identity to obtain the dimension of the full carrier.
The construction allows rank zero and reducible representations.

`effectiveUnitaryExpansion_eq_of_equiv` applies the linear coefficient map to
the published equality of exact classes from an actual invertible intertwiner.
Thus the constructed effective element is invariant under actual representation
isomorphisms, including independence of the supplied continuity and unitarity
proofs. Its definition already factors through the genuine exact quotient.

The `LocalWeil` declarations specialize these constructions and their full-class
and degree formulas to `Langlands.Weil.Local.localWeilGroup F` for any prime `p`
and actual `F : PadicField.{uF} p`. The carrier universe `uW` remains independent.
All local lattices, inclusions and exact groups are the existing actual ones;
no local group model or carrier resizing is introduced.

## Provenance and scope

This is internal derived packaging of the published effective unitary exact
expansion proof, the exact Jordan–Hölder coefficient map and the existing
unitary subset inclusion/extraction. All intrinsic identities follow from
these constructions and their proved identities.

The application is Henniart 2000, sections 2.4–2.5, printed pages 445–446
(PDF pages 7–8): the full local restriction of the unitary global Weil object
is placed in the free integral group on genuine positive-rank continuous
irreducible classes. Registered source: `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
This canonical coefficient packaging is a derived construction, not a separately
numbered source theorem. It adds no semisimplicity, finite-image, irreducibility
or positive-rank premise to the actual object.

No global associated object, local group map, automorphic unitary support,
absolute-global comparison, isometry, ambient lattice spanning or local Langlands
correspondence is constructed or assumed here. Its only import is
`Langlands.VirtualRepresentation.Weil.UnitaryExactExpansionProof`, which supplies
the already proved effective expansion and exact coefficient identities.
The prepared environment pins Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
