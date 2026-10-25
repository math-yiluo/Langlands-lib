# Algebraic transport of character-localized quotients

This module constructs small algebraic adapters for the existing quotient
`Jacquet.Localization.Coinvariants`. Its provenance is internal: every map is
obtained from the published quotient's universal property in
`Jacquet.Localization`. No geometric or analytic comparison is assumed or
proved here.

For representations of possibly different groups over a commutative ring,
`transportEquiv` takes a group equivalence between the localizing subgroups and
a linear equivalence between the coefficient modules. The input equalities say
that these maps intertwine the restricted actions and identify the characters.
It constructs a linear equivalence between the actual relation-span quotients.
The forward map sends the class of `v` to the class of its image under the
coefficient equivalence. The inverse uses the two inverse equivalences.
The proof applies the quotient universal property to each map and checks their
composites on the surjective quotient maps. Group, ring and both module
universes remain independent.

`restrictionEquiv` specializes this construction to restriction of the ambient
representation to the localizing subgroup, with localization at that group's
top subgroup. It is the identity on representatives.
`representationEquiv` specializes to an existing equivalence of representations
with the subgroup and character fixed. All three constructions have proved
evaluation formulas on quotient classes.

Over a field, `subsingleton_of_trivial_action` proves that the quotient vanishes
if some element of the localizing subgroup acts as the identity on every vector
but its character value is not one. The quotient relation says that every class
is annihilated by the nonzero scalar `1 - theta(u)`; scalar cancellation gives
zero. This argument uses neither topology nor smoothness nor finite dimension.

These adapters support the planned Whittaker heredity proof, but do not assert
heredity, find a non-open orbit witness, construct an open stabilizer, or
identify compact induction with its stabilizer localization. Those are separate
mathematical obligations.
