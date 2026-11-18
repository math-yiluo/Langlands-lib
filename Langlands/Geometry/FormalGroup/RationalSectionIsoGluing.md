# Gluing actual rational-section inverses

This internal construction supplies the sheaf gluing step for
`LocalQuasiIsogenyInverseStatement`. It uses the existing rational Hom
sheaf, its genuine restriction and composition operations, and the
already proved uniqueness of an actual two-sided inverse.

The coefficient ring O and the base O-algebra R are arbitrary commutative
rings. The O-algebra F is a field in the universe of R, and the two
coordinate types are finite. The scalar pi is arbitrary. No domain,
fraction-field, or uniform-denominator hypothesis is added.

`RationalSectionIso.existsUnique_of_cover` takes an actual forward
section z and an open cover on which its restrictions have actual
two-sided section inverses. The local isomorphisms agree on overlaps:
their forward sections are restrictions of z, and equality of forward
sections determines the whole isomorphism. Their inverse sections are
therefore a compatible family. The actual rational Hom sheaf glues this
family. Separatedness proves both inverse equations by checking them on
the cover. The resulting isomorphism restricts to each given local
isomorphism, and its uniqueness follows from its prescribed forward
section.

`existsUnique_locallyScalar_of_cover` additionally assumes that every
local reverse section is locally a scalar-power denominator of an
actual integral isogeny. The existing locality theorem for this
condition proves the same property for the glued reverse section.
`existsUnique_locallyScalar_of_locally` chooses one such witnessing
neighbourhood for every point of the open set and applies the cover
version. The exponents and neighbourhoods may vary with the point.

These are conditional gluing theorems. They do not construct integral
inverse numerators for arbitrary isogenies and do not by themselves prove
`LocalQuasiIsogenyInverseStatement`. Their provenance is the internal
sheaf-theoretic assembly needed by that published target, rather than a
quotation of a numbered theorem from external literature.
