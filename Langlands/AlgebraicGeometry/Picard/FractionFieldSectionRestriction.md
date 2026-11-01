# Section restriction to a chosen fraction field

This internal adapter works over `Spec R` for any domain
`R : CommRingCat.{u}` and any chosen fraction field `K : Type u` with its
given `R`-algebra structure and `IsFractionRing R K` instance. Let
`p : X ⟶ Spec R` be a scheme morphism.

`fractionFieldSectionRestriction R K p` restricts actual sections of `p`
along `Spec.map (CommRingCat.ofHom (algebraMap R K))`. Its values are
actual morphisms `Spec K ⟶ X` together with their equations over
`Spec R`.

`fractionFieldGenericSectionEquiv R K p` identifies generic residue-field
maps over `Spec R` with these chosen-fraction-field maps. Its forward map
precomposes with the hom of the published
`fractionFieldGenericPointIso R K`; its inverse precomposes with the
inverse. The compatibility theorem for that isomorphism proves both
equations over the base. The inverse identities follow by cancellation
and subtype extensionality.

`fractionFieldGenericSectionEquiv_restriction` states that this
equivalence carries `genericSectionRestriction p` to
`fractionFieldSectionRestriction R K p`. Associativity and the published
base compatibility equality prove it. Consequently
`fractionFieldSectionRestriction_injective` follows from separatedness
and `genericSectionRestriction_injective`.
`fractionFieldSectionRestriction_surjective_iff` proves that extension
existence for canonical generic maps is equivalent to extension existence
for the specified fraction-field maps. The two directions use the
equivalence and the compatibility with restriction.

The provenance is internal composition of the published generic-point
isomorphism and section-restriction construction. There is no new
literature claim. Neither the equivalence nor the surjectivity equivalence
asserts that sections extend. No valuation, noetherianity, rank, finite
type or unibranchness condition is required; separatedness is used only
for injectivity. The construction preserves the arbitrary universe and
the chosen fraction-field algebra map used in the two-axis extension
target.
