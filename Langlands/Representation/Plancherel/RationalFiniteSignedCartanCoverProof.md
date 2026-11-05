# Proof of finite signed Cartan charts on actual rational points

The proof is internal. It applies `finiteSignedChamberLattice` to the actual
cocharacter lattice of the supplied maximal split torus, with its actual
simple-root pairings. The split-torus coordinate results provide finite
generation and torsion-freeness. The supplied standard-cocharacter statement
provides the standard elements required by the lattice theorem.

The supplied standard-Levi compatibility gives both the actual Cartan
decomposition for the full Levi and the uniformizer valuation identity.
`levi_univ_eq_top` identifies that full Levi with the whole rational-point
group. `exists_rep_rationalCartanSet` gives a common integer lower bound for
the simple-root pairings of the cocharacters occurring in its middle
representatives, together with a translate from the image of the supplied
finite lattice transversal.

Apply the signed lattice cover at that lower bound. Its generators are
independent and weakly positive in every chart. Its finite lattice
translates, evaluated by `uniformizerPowers`, multiply the finite rational
translates to give `T`. The uniformizer homomorphism respects addition, and
its values commute because its domain is commutative. These two facts put
each rational point in the exact product order in the statement.

The common pairing kernel stays inside the signed charts throughout the
proof. No arbitrary central rational point is introduced, and no central
character or finite-length hypothesis is used. Empty roots and zero kernel
rank are handled by the same finite-sum argument. The proof does not
construct any of its supplied geometric witnesses or a simultaneous
compact-open basis, and does not prove a coefficient or matrix-norm bound.
