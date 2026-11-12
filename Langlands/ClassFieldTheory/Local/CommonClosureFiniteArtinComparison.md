# Finite Artin restrictions of the common-closure family

`candidateFiniteRestriction` composes a candidate's unit map into the
actual fixing-subgroup abelianization with actual restriction to a finite
Galois overfield. The finite overfield is Galois over the original base and
contains the chosen intermediate field.

`candidateFiniteRestriction_familyOfStandalone` identifies this map for
every supplied family of standalone geometric reciprocity equivalences:
its value at a unit is the concrete `abelianizedArtinSymbol` at the
inverse unit. `candidateFiniteRestriction_constructed` specializes this
identity to the unconditionally constructed common-closure family.

The proof embeds the finite overfield in the intermediate field's own
algebraic closure by composing literal inclusion with the inverse of
`intermediateClosureEquiv`. The defining Galois intertwining identity
proves that actual finite restriction commutes with
`intermediateGaloisEquiv`. Quotient induction gives the same identity
after closed-commutator descent. The proved formula
`galoisHom_familyOfStandalone` then reduces the comparison to
`closureFiniteAbelianRestriction_geometric`.

The normal and finite-dimensional certificates for the finite overfield
over the intermediate field follow from the original finite Galois
extension. No normality of the intermediate field is assumed. This
internal transport result does not use an inverse-cup comparison or
arithmetic transfer premise.
