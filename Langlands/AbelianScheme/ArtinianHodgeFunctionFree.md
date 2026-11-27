# Freeness of the function end over an Artinian base

Inversion commutes with base change of the abelian scheme. On the
preimage cover of the special fibre, the tensor equivalence of function
cochains therefore intertwines inversion and the Čech differential.
The two sign summands correspond under the projected equivalences.

The positive summand is exact in degree one on the residue fibre. It
remains exact over the local Artinian ring by `exact_of_residue_exact`.
For the negative summand, the residue differential out of degree zero
is injective and the complex is exact in degree two. By
`free_h1_of_residue` the degree-one quotient is free. Its inclusion into
full function cohomology is injective because an available primitive
can be projected to the negative summand. It is surjective because
the positive part of any cocycle is a coboundary. The fixed-cover
comparison `structureH1Equiv` transfers the freeness from the doubled
cover to the supplied one.

This proves freeness of the function end in the situation of Lan's
Hodge sequence (2.1.6.6), *Arithmetic compactifications of PEL-type
Shimura varieties*, revision of 14 March 2021, §2.1.6, printed p. 135
(PDF p. 163). The retained source is `lan-2008-pel-thesis-revision-2021`,
SHA-256 `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
