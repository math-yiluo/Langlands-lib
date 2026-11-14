# Ambient isomorphisms of relative Levi subgroups

This internal derived unit transports the existing
`IsRelativeLeviSubgroup` predicate through an isomorphism of its ambient group
scheme. The base scheme and its universe are arbitrary. It supplies a formal
transport step for the relative conjugacy argument; it asserts no existence
of Levi subgroups, maximal tori, or conjugating points.

`IsRelativeLeviSubgroup.comp_iso` takes a relative Levi inclusion `l : L ⟶ P`
and an isomorphism `e : P ≅ P'`. It proves that `l ≫ e.hom` is a relative
Levi subgroup of `P'`. Closedness transports through the ambient isomorphism,
and the smooth source `L` is unchanged. The radical witness `r : U ⟶ P`
in the given Levi predicate is replaced by `r ≫ e.hom`; the relative radical
transport theorem preserves its complete predicate.

The published equality `subgroupMultiplication_postcomp` identifies the new
multiplication morphism with the original morphism `L ×_S U ⟶ P` followed by
the underlying isomorphism `P ⟶ P'`. Both factors are isomorphisms of schemes
over the base, which proves the required multiplication isomorphism.
This argument uses the actual scheme morphism, without treating subgroup
multiplication as a group homomorphism.

`IsRelativeLeviSubgroup.comp_iso_iff` applies this transport to `e` and its
inverse. The resulting reverse composite of inclusions equals the original
inclusion by the isomorphism identities.

`RelativeLevi.ambientTransportEquiv L e` is the resulting equivalence between
the subtypes of relative Levi embeddings of a fixed group scheme `L` into
`P` and `P'`. Its forward function postcomposes with `e.hom`, and its inverse
postcomposes with `e.inv`. The two transport lemmas establish membership in
the respective subtypes. The inverse laws follow from the isomorphism
identities and equality of subtypes with the same underlying morphism.
This construction identifies embeddings with their complete relative Levi
predicate; it introduces no choice of subgroup representative.

The provenance is internal: these constructions combine `RelativeLevi.Basic`,
`RelativeLevi.UnipotentRadicalConstructions`, and the multiplication equality
in `Rational.LeviAmbientTransport`. No additional geometric hypothesis or
literature assertion is introduced. In particular, specialization to an inner
automorphism proves preservation under conjugation once that automorphism
is supplied.
