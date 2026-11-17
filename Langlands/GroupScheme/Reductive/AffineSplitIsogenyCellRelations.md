# Actual powered cell relations over local coefficient rings

This internal supporting unit combines the actual powered Weyl and word
laws with the arbitrary-target cell reductions. The coefficient ring is
commutative and local. The source and target are affine, their coordinate
tori are closed, and genuine normalized simple-root data are supplied
for corresponding bases and transported source words. The positive
systems correspond, and the positive source roots are enumerated by
increasing height. The original characteristic condition on the
root-datum isogeny is retained.

Genuine target all-test rank-one laws transfer to the powered maps under
the prescribed torus map, with the literal source coroot. Individual-root
equivariance gives their literal negative-simple source character.
These prove `TargetNegSimpleLaws` without a powered-parametrization premise.

The proved common Weyl units and complete target word laws give all
positive commutator formulas. Source geometry converts them to positive
factor and simple-root cell-translation laws. The arbitrary-target
negative-simple reduction gives the other simple-generator laws.
Together they imply root-translation transfer for every member of the
two Weyl families. Torus equivariance then supplies torus translation
and hence full multiplication compatibility of the two actual cell maps.
`PoweredLocalCellCompatibilityStatement` states this full result, and
`poweredLocalCellCompatibility` proves it in every universe.

Only the genuine source cell is used as an open immersion. The powered
target cell is not assumed open, injective, or to parametrize its roots.
Descent from local coefficient rings to an arbitrary affine base and
the final ambient isogeny theorem remain separate obligations.
