# Canonical root containment after integral reduction and quotient

This derived adapter works in any universe over a local domain with specified
fraction field. It uses a supplied relative-component model, a compatible
integral torus and a splitness witness for that torus. The neutral model is
smooth by its supplied model data.

For every nonzero generic character `a`, `reduction_mem_rootFunctor` places
the reduction of each integral neutral-model section with generic point in
`rootGroupPoints i a` in the intrinsic residue root functor for
`T.characterSpecialization hT a`. This is the canonical specialization through
the same integral torus, rather than an arbitrarily chosen lattice map.

The proof takes the inverse image of `a` under `genericCharacterEquiv`.
The supplied generic torus square transports its generic root functor to the
one for `a`. `SplitRootReduction.reduction_mem_of_generic_mem` gives residue
root membership, and character-specialization compatibility identifies that
residue character with the required specialization.

`quotient_reduction_mem_rootFunctor` composes this membership with the actual
special-fibre projection using functoriality of intrinsic root groups.
`quotientRootReduction` restricts reduction followed by this projection to the
subgroup of integral sections whose generic point is in the original root
group. Its codomain is the corresponding intrinsic quotient root group;
`quotientRootReduction_coe` records the original image.

Only the named existing interfaces and the derived `SplitRootReduction`
construction are used. The quotient data need not satisfy the reductive-quotient
predicate for these containment assertions. No Henselian or algebraically closed
residue-field hypothesis, maximality clause, root-survival assertion, strict-depth
kernel description or facet criterion is used or concluded.
