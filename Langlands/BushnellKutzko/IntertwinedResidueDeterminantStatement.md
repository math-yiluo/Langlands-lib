# The residue determinant of an intertwined character

In the proof of (5.2.2)(ii), Bushnell and Kutzko deduce the determinant
factorization of a character of `U(𝔅)/U¹(𝔅)` from intertwining by all of
`Bˣ` on printed p. 175 (PDF p. 187). The chain and its order are defined
in (1.1.1)–(1.1.2), printed p. 20 (PDF p. 32). The unit filtration is
defined on printed p. 21 (PDF p. 33). Proposition (1.2.4), printed p. 25
(PDF p. 37), identifies `𝔅` as the order of the chain over the parameter
field. The criterion can therefore be stated for a lattice chain over
a general nonarchimedean local field. The retained source for
*The admissible dual of GL(N) via compact open subgroups* (1993),
`bushnell-kutzko-1993-admissible-dual-gln`, has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`IntertwinedResidueDeterminantStatement` fixes a chain `L` over the valuation
ring of `F` in the vector space `V`. The universes of `F` and `V` are
independent. A character `ξ` of `L.unitFiltration 0` is assumed trivial
on `L.unitFiltration 1`. For each ambient automorphism and each element of
`L.unitFiltration 0` whose conjugate still belongs to that group, the
intertwining hypothesis equates the two character values. Then there is a
character `χ` of the residue field units such that for each `x` in the
original unit group and each valuation-ring unit `a` representing `det x`,
`ξ x` is the value of `χ` on the reduction of `a`.
