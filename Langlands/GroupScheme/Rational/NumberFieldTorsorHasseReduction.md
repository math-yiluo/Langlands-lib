# Rational points on torsors and the number-field Hasse kernels

`NumberFieldTorsorHasseFor F G` asserts the Hasse principle for rational
points of affine smooth surjective `G`-torsors over a number field `F`.
The torsor carries an actual left action with the torsor map
`G × X → X × X` an isomorphism. A local point over `F_v` is a morphism
`Spec F_v → X` over `Spec F`, using the Library's completion at `v`.
A global point is a section of `X → Spec F`.
`NumberFieldSimplyConnectedTorsorHasseStatement` and
`NumberFieldAdjointTorsorHasseStatement` give this assertion for the
two corresponding classes of semisimple group schemes.

This formulation is derived from Milne, *Algebraic Groups* (2017).
Section 2(g), pp. 60–61, describes torsors and the neutral class given
by torsors with a point. Proposition 3.50, p. 80, identifies first Galois
cohomology with torsors for smooth groups. Theorem 25.64(a,b), p. 562,
compares the classes at all completions. Applying it to the neutral
class gives the rational-point assertion. Affineness and smoothness
of torsors of affine smooth groups follow by descent, as in Proposition
2.69. The Lean hypotheses make these properties and the torsor map
explicit. The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The two proved kernel comparisons use the actual affine smooth torsor
of a natural cocycle. If the base-changed cocycle is trivial over a
completion, its cochain over the pullback cover corrects the chosen
point of that torsor. The corrected point agrees over both projections
of every pair with the same new-base coordinate. Effective epimorphy
descends it to a point over the completion. A global point from the
torsor Hasse hypothesis trivializes the original cocycle by the published
torsor-section criterion.
