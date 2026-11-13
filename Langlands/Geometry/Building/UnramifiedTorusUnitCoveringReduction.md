# Rational covering from the torus-unit geometric inputs

`UnramifiedTorusUnitCoveringReductionStatement` says that the two geometric
prerequisites `UnramifiedFixedPointSplitTorusStatement` and
`UnramifiedTorusUnitFixedApartmentStatement` imply exactly
`UnramifiedGaloisFixedBuildingPointStatement`, at every universe level.
`unramifiedTorusUnitCoveringReduction` proves this implication. It does not
prove either geometric premise, so it does not yet prove the covering target
unconditionally.

For a coefficient-fixed point \(y\), the first input provides a maximal
\(F\)-split torus \(S'\) whose \(K\)-unit subgroup fixes \(y\).
The published theorem `smoothMaximalSplitTorusConjugacy` supplies
\(g\in G(F)\) and a source isomorphism conjugating the chosen torus \(S\)
to \(S'\). The group is smooth, affine, and connected by its connected
reductivity hypothesis. Set \(z=g_K^{-1}y\).

The elementary transport lemma in `TorusUnitFixedPoint` shows that the
\(K\)-units of \(S\) fix \(z\). Semilinearity of the actual coefficient
quotient action, together with coefficient fixation of extended rational
points, shows that \(z\) is coefficient-fixed. The second input now gives
a coefficient-fixed apartment point \(x\) with apartment image \(z\).
Applying \(g_K\) gives the target equality.

This is an internal derived reduction. The two geometric inputs carry their
own source citations to Kaletha–Prasad 9.3.8 and 9.3.13 and the authors'
corrections. This proof uses no full building-descent statement, no reduction
to full building descent, and no consumer of such a statement. The module
declaring the target is imported solely to name the target proposition.
