# Adjacent-rank gamma from complete unramified transport

This internal implication isolates the remaining prerequisite for the exact
adjacent-rank gamma base. Its premise is
`UnramifiedTwistGammaStatement.{uF,uV,uW}` and its conclusion is the unchanged
`TwoBlockGammaAdjacentRankStatement.{uF,uV,uW}`. The module proves this
implication; it supplies neither a proof of the premise nor the closed
adjacent-rank theorem.

The proof applies `adjacentRankUpperGamma_of_lowerCharacter` to the original
dependent upper family. It discharges that theorem's arbitrary-character
lower analytic premise with
`adjacentRankLowerCharacterGamma_of_transport`, using the supplied gamma
transport proposition. The latter lower theorem uses retained-kernel
continuation of actual original and translated dual integrals and compares
the resulting equation with a nonzero witness from a complete ambient
gamma certificate.

The upper-family theorem derives `m 1 = r` from the rank sum and the exact
restrictions `t = r+1` and `m 0 = 0`. It identifies the original first
rank-one block with a lifted scalar character, then uses
`glOppositeProductReversal` and the size adapter to compare the actual
normalized inductions after reversing the complete ordered family of
sizes, carriers, module structures and representations. Complete block and
induced gamma certificates transport through these equivalences. Only
after this representation comparison does commutativity identify the
finite product in upper order with the product in lower order.

The result preserves independent field, test and block universes, the
supplied additive character and self-dual Haar measure, and arbitrary
full Whittaker-type inputs, including reducible representations. Compatible
measure existence, nonzero functional and rational witnesses, and all
universal certificate clauses are retained. This is a derived composition
of the named lower analytic theorem and actual ordered-family transport;
it uses no unrestricted multiplicativity or later rank descent.
