# Finite orthant coordinates by Euclidean division

`Langlands.finiteChamberLattice` proves the complete
`Langlands.FiniteChamberLatticeStatement`, with independent universes for the
finite label type and the additive commutative group.

Apply the standard-vector hypothesis to the complement of each label to choose
a generator whose diagonal pairing is a positive integer and whose other
pairings vanish. These generators are chosen before the chamber bound.

For an arbitrary integer bound `B` and a vector in the lower-bounded chamber,
divide each shifted pairing `pair α x + B` by the positive diagonal pairing.
The shifted pairings are nonnegative, so the integer quotients have natural
number representatives. Subtract the corresponding sum of generators.
Additivity and the off-diagonal vanishing identify the new pairings with the
Euclidean remainders minus `B`. They lie in a finite product of integer intervals.

The image of the bounded remainder set under the tuple of pairings is therefore
finite. The proof chooses one actual vector for each attained tuple, using
`Function.invFunOn`. The difference between the remainder vector and its
representative has zero pairing with every label. Additive group algebra gives
the claimed decomposition. The same proof includes empty labels and bounds of
either sign, without a freeness or finite-generation premise.

This is an internal algebraic derivation of the published statement. It proves
no centrality, Cartan cover, Haar-volume estimate or coefficient bound for an
actual reductive group; those remain separate application obligations.
