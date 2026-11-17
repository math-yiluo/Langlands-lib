# Fundamental weights under the actual kernel torus map

This internal construction packages character restriction along the actual
torus morphism supplied by `TitsIndexData.KernelComparison`. It uses that
published comparison's torus map, coroot equality and vertex equivalence.
It does not replace these by a diagram map or an independently supplied
linear transformation.

`KernelComparison.torusMap` chooses the torus morphism in the comparison.
`KernelComparison.weightRestriction` is actual character precomposition
after base change to the separable closure. The simple-coroot pushforward
identity is the corresponding conjunct of the comparison. The adjointness
of actual character restriction and cocharacter pushforward therefore
computes the pairing of a restricted character with every simple kernel
coroot.

If the coroot spans of both root data are the full integral cocharacter
lattices, simple coroots are integral bases. Comparing all these pairings
then proves two identities. An ambient fundamental weight at a zero vertex
restricts to the fundamental weight at its corresponding kernel vertex.
An ambient fundamental weight at a distinguished vertex restricts to zero.
The proof uses the actual perfect pairings to deduce equality of integral
characters.

These statements hold for arbitrary actual kernel comparisons, with no
Cartan-type, star-triviality or field-characteristic restriction. The
coroot-span conditions are explicit hypotheses; this module asserts no
additional simply-connectedness criterion.

The construction is derived directly from the published
`KernelComparison` and fundamental-weight APIs. It proves only lattice
restriction identities. It does not construct a Tits obstruction or prove
equality of ambient and kernel Brauer classes.
