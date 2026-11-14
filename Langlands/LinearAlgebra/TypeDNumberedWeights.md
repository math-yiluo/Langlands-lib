# Numbered vector weights in an integral type-D weight lattice

This internal construction starts with an actual root datum whose coroots span
the whole integral cocharacter lattice, a supplied root base, and a numbering
of its simple vertices by `Fin n` with Cartan matrix `D n`, for `n ≥ 4`.
It defines the vector weights by their values on the integral simple-coroot
basis. The perfect pairing supplies a character for each such integral
functional.

The coefficients are the pairings of the standard coordinate weights with
`e_j-e_(j+1)` at the chain vertices and with `e_(n-2)+e_(n-1)` at the final
vertex. Direct arithmetic identifies their successive differences and their
final sum with the rows of the published Cartan matrix. Extensionality on
the simple-coroot basis gives the corresponding root identities. The first
weight takes value one at the vertex numbered zero and zero at every other
simple coroot.

These are derived integral lattice calculations. The module neither identifies
the weights of a supplied representation nor descends them across a central
cover. It uses no classification theorem and treats rank four by the same
formulas as every higher rank.
