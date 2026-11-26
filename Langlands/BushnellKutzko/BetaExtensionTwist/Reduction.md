# The beta-extension twist

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), Proposition (5.3.2), printed pp. 176–177, uses the Heisenberg
support and multiplicity-one assertions in Propositions (5.1.1) and (5.1.8).
The retained source `bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`BetaExtensionTwistReductionStatement` is the implication from
`HeisenbergRepresentationStatement`, `SimpleStratumLatticePropertiesStatement`
and `SimpleStratumGroupPropertiesStatement` to `BetaExtensionTwistStatement`.
It retains the five independent universes. The accompanying theorem
`betaExtensionTwist_of` proves the implication. The Heisenberg character trace and common-domain
index yield multiplicity one on `Bˣ`. The equivalence between the
restriction of `κ` to `J¹` and `η` transports both support and dimension.
The level-zero carrier formula supplies the common-domain factorization.
The tensor intertwiner calculation then gives the double coset support
and the equality of dimensions for `κ ⊗ ξ` and `ξ` at `Bˣ`.

`isIrreducible_betaExtension_tprod` proves irreducibility directly for
an extension of a Heisenberg representation and a finite-dimensional
irreducible complex representation `ξ` trivial on `J¹`. The
restriction of `κ` to `J¹` is equivalent to the finite-dimensional
irreducible `η`. The tensor irreducibility lemma applies to these
restrictions and the irreducibility of `ξ` on all of `J`.
