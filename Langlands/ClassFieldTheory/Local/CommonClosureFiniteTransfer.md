# Finite restriction and fixing-subgroup transfer

This internal construction proves that finite Galois restriction commutes
with the actual transfer between literal common-closure fixing subgroups.
`finiteTransferHom` is the common-closure transfer followed by finite
restriction to the algebraic abelianization of the relative Galois group.
Its comparison theorem `finiteAbelianRestriction_transfer` identifies this
composite with finite restriction followed by `relativeGaloisAbelianTransfer`.

The original base is any perfect field. The finite top field is Galois
over this base and contains both finite intermediate fields. The middle
field need not be normal. All algebras used for the inclusions are
installed explicitly from the literal intermediate-field inclusions.

The relative Galois subgroup consists exactly of the automorphisms fixing
the middle field's image. The action formula for finite restriction shows
that its preimage is precisely the nested common-closure fixing subgroup.
Restriction also commutes with restriction of scalars.

The proved double-coset transfer formula, with one representative and
surjectivity of finite restriction, gives `finiteRestriction_transfer`
on actual automorphisms. The identification of the subgroup with the
relative Galois group uses `relativeGaloisSubgroupEquiv`. Quotient induction
then gives the comparison on topological abelianizations. Postcomposition
commutes with the actual finite-coset product, so this passage preserves
the transfer specified by the existing common-closure and finite
definitions.

The construction and proof are derived from the existing restriction,
transfer and closed-commutator interfaces. No arithmetic reciprocity
identity is assumed or concluded in this unit.
