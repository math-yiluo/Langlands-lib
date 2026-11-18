# Cocharacter tangent actions on actual representation weights

For a split pinning `p`, a finite matrix representation `r` and a cocharacter
`y` of the supplied maximal torus, `representationCocharacterAction p r y`
is the tangent endomorphism obtained by mapping the actual cocharacter
tangent through the torus inclusion and `r`.

`representationCocharacterAction_apply` proves that this endomorphism acts
on the actual weight space of `mu` by the integer pairing
`p.rootDatum.toLinearMap mu y`, cast to the field. The proof applies the
character-space differential formula to the restricted representation,
uses the exact character value on the cocharacter tangent, and identifies
the canonical lattice pairing with the root datum pairing through
`p.isRootDatum.1`.

In characteristic zero, if `sigma` is monomorphic, every nonzero cocharacter
pairs nontrivially with an actual weight of `sigma`
(`exists_weight_pairing_ne_zero_of_mono`). Otherwise the tangent action
vanishes on every weight space, hence on the whole representation by its
published torus weight decomposition. Injectivity of the tangent map of
`sigma` and of the torus inclusion makes the cocharacter tangent trivial.
The characteristic-zero injectivity theorem for cocharacter tangents then
makes the original cocharacter zero, a contradiction.
The closed-subgroup version applies the published monicity theorem.

## Provenance

This is an internal derived helper for the group-side Lie-weight input in
Task 7128. It uses actual all-algebra character spaces, actual tangent maps
and the unchanged root datum on the supplied torus. It assumes no
Freudenthal or Weyl character formula.
