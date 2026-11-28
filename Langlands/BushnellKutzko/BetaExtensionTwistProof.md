# Intertwining and irreducibility of the beta-extension twist

`betaExtensionTwist` proves `BetaExtensionTwistStatement` for a simple
stratum at level zero over a nonarchimedean local field, a
Bushnell–Kutzko additive character, a defining-sequence choice, a simple
character `θ`, a Heisenberg representation `η` over `θ`, a beta-extension
`κ` of `η` and a finite-dimensional irreducible `ξ` trivial on `J¹`.
The base field, stratum space and carriers of `η`, `κ` and `ξ` have five
independent universes.

The source is Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), Proposition (5.3.2), printed pp. 176–177
(PDF pp. 188–189). The retained source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The proof applies `heisenbergRepresentation_of` to
`simpleCharacterPairing`, `simpleCharacterIntertwining` and
`simpleStratumGroupProperties`. The resulting Heisenberg theorem supplies
the scalar action of `H¹`, the degree formula
`(dim η)² = [J¹ : H¹]` and the intertwining support `J¹ B_β^× J¹`.
The proof applies `betaExtensionTwist_of` to this theorem and to
`simpleStratumLatticeProperties` and `simpleStratumGroupProperties`.

For a centralizing unit `y`, the level-one trace-dual calculation and a
projection preserving both radical steps show that the index of
`H¹ ∩ y⁻¹H¹y` in `J¹ ∩ y⁻¹J¹y` is at least `[J¹ : H¹]`.
On the Heisenberg intertwining support, a finite-quotient character
average gives the square of the degree as the product of the
common-domain index and the intertwining dimension. The index bound
extends across each `J¹` double coset and makes the dimension at most
one. It is positive on the support, giving multiplicity one.

A nonzero tensor intertwiner yields a nonzero Heisenberg intertwiner
by taking matrix coefficients on the `ξ` factor after restriction to
the common domain in `J¹`. This places the tensor product support in
`J¹ B_β^× J¹`. For a centralizing unit, a nonzero beta-extension
intertwiner restricts to a generator of the Heisenberg intertwining line.
Tensoring with this map gives a linear equivalence from the full
intertwining space of `ξ` to that of the twist and proves the equality of
dimensions. The common domain in `J` factors as the product of the
common domains in `U(𝔅_β)` and `J¹`. Both actions of `J¹` on `ξ` are
trivial on the common domain, so intertwining of `ξ` reduces to the
`U(𝔅_β)` factor. Double-coset invariance gives the support
`J · I_{B_β^×}(ξ | U(𝔅_β)) · J`.

For irreducibility, the restriction of `κ` to `J¹` is equivalent to the
finite-dimensional irreducible `η`. Burnside's theorem and the
triviality of `ξ` on `J¹` make every invariant tensor subspace stable
under all endomorphisms acting on the `κ` factor. Composing a tensor
action of `J` with the inverse action on the `κ` factor isolates the
action on `ξ`. Burnside's theorem for the finite-dimensional irreducible
`ξ` gives stability under all endomorphisms on the second factor.
Products of the two families of endomorphisms span the endomorphisms
of the tensor space, so any nonzero invariant subspace is the whole
space.
