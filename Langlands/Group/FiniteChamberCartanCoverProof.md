# Orthant Cartan charts and empty-label compactness

`Langlands.finiteChamberCartanCover` proves the complete
`Langlands.FiniteChamberCartanCoverStatement`, with three independent universes.

Apply `finiteChamberLattice` to the integral pairings and standard vectors.
For the supplied chamber bound it gives a finite set of lattice remainder
representatives. Multiply their images by the original finite set `F₀` to form
the finite set `T`.

Decompose the lattice coordinate of each original Cartan representative into
a remainder, a natural-number generator sum and a common-kernel vector.
The homomorphism sends this sum to a product of commuting factors. Its
common-kernel image is central by hypothesis, so it can be moved to the right
of the original Cartan expression. Combining the remainder image with the
finite translate gives the asserted charts modulo the full center.

If the label type is empty, each generator sum is zero. The compact set
`K * T * K` therefore meets every full central coset.
`Induction.compactSpace_quotient_of_compact_representatives`, applied to
`Subgroup.center G`, gives compactness for the actual right-coset quotient
with its canonical topology.

This is an internal deduction. The proof keeps the supplied Cartan cover
and the central-kernel comparison as premises; it proves no actual reductive
existence statement, Haar-volume bound or square-integrability result.
