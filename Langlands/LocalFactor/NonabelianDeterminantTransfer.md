# Determinant transfer and common-closure reciprocity

This derived helper module connects the actual finite-coset transfer to the
supplied common-closure reciprocity family. It uses the published topological
abelianization, finite-index subgroup transfer, and exact virtual induction
constructions, together with the algebraic helper in
`VirtualRepresentation.ExactDeterminantInduction`.

`abelianizationLift_map_apply` proves naturality of continuous character descent
through the closed-commutator quotient by quotient induction. At a genuine
group element both sides are the same character value.
`character_subgroupTransfer_apply` compares evaluation of the finite-coset
transfer by a continuous character with evaluation on the actual abelianized
subgroup transfer. Unfolding the latter construction reduces this to naturality
and postcomposition with the finite transfer product.

`exists_reciprocityUnits_eq` proves that any unit has a Weil lift for a supplied
reciprocity equivalence: choose a representative of its inverse image in the
actual topological abelianization. No reciprocity equivalence is constructed.
`character_transfer_reciprocity` applies the transfer/inclusion square contained
in the given `NormalizedReciprocity` hypothesis. The equivalence on the larger
field is injective, so the square identifies the transferred quotient class
with the quotient class of any compatible Weil lift. The preceding character
transfer identity then identifies the character values.

`determinant_induce_degreeZero_reciprocity` applies the conditional exact
Gallagher descent to the restricted virtual representation used by actual
common-closure induction. Restriction preserves the degree and transports the
determinant by precomposition. Its actual virtual determinant is continuous by
the published determinant continuity theorem, so it is a character to which
the preceding reciprocity result applies. Thus the determinant of degree-zero
induction at a Weil lift equals the original determinant at any lift of the
included field unit.

The final result retains the full genuine `GallagherDeterminantStatement` as an
explicit hypothesis, as well as the supplied normalized reciprocity relation.
It does not assert Gallagher's theorem, reciprocity existence, generation or
the final additive-character scaling proposition. The group and field
constructions and the independent representation universe remain those of the
published common-closure interface. All provenance is internal algebraic
derivation from the named modules; no new source translation is made.
