# Descent of numbered character families along split-torus base change

This internal derived module transports supplied characters and their equations
back through the canonical character-lattice base-change equivalence of a split
torus. The base map is any morphism between spectra of integral domains. There is
no characteristic, field-cardinality, or algebraic-extension restriction.

`characterLattice.descendFamily` takes characters of the actual base-changed
torus and applies the inverse of `characterLattice.baseChangeEquiv` to each one.
`baseChange_descendFamily` identifies their pullbacks with the original family.
The construction uses the existing canonical equivalence and introduces no
coordinate choice on the torus.

`latticePairing_descendFamily` proves that the descended characters have the same
integer pairings against original cocharacters. Its proof applies the published
base-change identity for the pairing. `latticePairing_restrict_descendFamily`
also restricts the characters along a supplied morphism S to T; associativity
of the actual composition gives the comparison. The group scheme S need not be
split. `signed_weight_card_descendFamily` identifies the fibers indexed by pairs
of a family index and an integer unit, with weight the signed pairing. It uses
the identity on the indexing pairs, linearity of the pairing in the character,
and the preceding restriction identity. No finite-index hypothesis is needed
for equality of these cardinalities.

`SplitRootDatum.numbered_roots_descend` retains a supplied root datum P on the
original split torus, a base B, a numbering by Fin n with n at least two, and a
family eps on the extended torus. It assumes the consecutive-difference and
terminal-sum simple-root equations, and existence of every signed pairwise-sum
root, in the canonically transported root datum. It proves all three equations
for the descended family in P with the same base, numbering, and root indices.
The proof applies injectivity of the character-lattice equivalence and its
compatibility with subtraction, addition, and integer multiples.

The provenance is internal: the definitions and proofs are deductions from
`Torus.SplitLatticeBaseChange` and `Reductive.RootDatumBaseChangeStatement`.
They construct neither the extended character family nor an eigenbasis, and
prove no type-D classification or existence statement. They supply the character
descent step for the host spin-cover vector-weight proof once its split-model
characters and eigenbasis have been constructed.
