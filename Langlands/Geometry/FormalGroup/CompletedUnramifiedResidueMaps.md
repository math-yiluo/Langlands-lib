# Completed unramified coefficient maps on Nilp

`Nilp.completedUnramifiedResidueMapEquiv` gives the natural bijection between
maps from the actual completed unramified integer ring to a nilpotent test
and maps from the actual unramified residue field to its uniformizer reduction.
The residue field has the original base residue algebra structure and is an
algebraic closure for that structure.

For the uncompleted integers, reduction factors through their residue field
because the base uniformizer generates the upstairs maximal ideal. Conversely,
formal étaleness lifts the given residue map uniquely through the nilpotent
ideal of the test. Restriction from the completion is already a bijection.
The composite equivalence recovers actual reduction on completed coefficients
and commutes with every morphism of tests.

Drinfeld uses this coefficient base and reduction in *Coverings of p-adic
symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3). The comparison here
expresses those residue coordinates using the actual completed base.
