# Level-one adjoint trace duality

The level-one case of Bushnell–Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (3.1.19) and the middle exactness in (3.1.16),
printed pp. 95–97, identifies the dual of the `H¹` lattice as the sum of
the `J¹` commutator image and the order. The retained source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The proof works with maximal-ideal trace duals for a level-zero stratum
admitting the supplied defining-sequence choice. It proves both the
full formula and the equality of the dual's commutator-image part with
the image of the level-one `J` lattice. The full formula follows from
the latter equality by the radical-preserving centralizer projection.
Both level-one layers contain the level-one centralizer lattice by their
recursive definitions.

For a terminal element of depth `n`, duality exchanges the `H` cutoff
step with the step of degree `1 - simpleHCutoff n`. Adjoint lattice lifting
moves a preimage into the `J` cutoff step by subtracting a centralizing
endomorphism. The reverse inclusion follows by the filtration bound on
multiplying by the terminal element.

In the recursive step, duality on the intersection with the `H` cutoff
step writes a test adjoint as an adjoint for the next element plus a
filtration term. The next cutoff bounds put the first term's preimage
in the `J` cutoff step after removing its centralizer component. Adjoint
lifting at the current critical depth then adjusts the original preimage
into that step. On this step the two adjoint maps differ by an element
annihilating the current `H` cutoff. The induction hypothesis for the
next element puts the adjusted preimage in its `J` lattice. The converse
uses the same adjoint congruence and the trace annihilation of the
centralizer term.

`simpleLayer_traceDual_adjoint` extracts the normalized-field witnesses,
monotone critical depths, equivalence bounds and terminal depth from a
`DefiningSequenceChoice` at stratum level zero. The argument uses the
scalar terminal convention through the bottom critical exponent. It
uses no additional lattice hypotheses on the stratum.
