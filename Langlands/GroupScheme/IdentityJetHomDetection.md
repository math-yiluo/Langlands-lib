# Detection of homomorphism equality by an identity jet

`DetectsBaseChangeHomEq` is the all-base-change implication from agreement
on the identity neighborhood of a fixed order to equality of two group
homomorphisms. It packages an internal comparison used to detect the
kernel of the conjugation action through an identity jet.

Over a quasi-compact base, consider two homomorphisms from a smooth
separated group with geometrically irreducible fibres to a separated
locally finite type group. `exists_order_detects_baseChange_hom_eq`
gives one order for which the implication holds. The order can depend
on the original homomorphisms.

The proof takes the closed equalizer of the original maps and applies
uniform finite-jet detection to its kernel ideal near the unit
section. Agreement on the changed jet then gives agreement on an open
neighborhood of the entire changed unit section. The open-cell group
homomorphism comparison propagates agreement to the whole source.
