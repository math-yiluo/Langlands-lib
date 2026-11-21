# Pointwise cuspidality of continuous representatives of full AE cusp classes

Let `Q` be the Library's positive-central rational quotient with its
canonical measure `μQ`. Use the split-centre data identifying it with the
norm-one quotient, and the existing parabolic dynamics and connected
reductivity hypotheses specifying the proper rational parabolics and their
compact radical quotients. Suppose `f : C(Q, ℂ)` represents `φ : Lp ℂ 2 μQ`
almost everywhere. `GroupSchemeFullAEL2ContinuousCuspidalityStatement`
asserts that `φ` lies in the full almost-everywhere cuspidal submodule if
and only if the pullback of `f` has zero canonical proper parabolic
constant term at every adelic point.
`groupSchemeFullAEL2ContinuousCuspidality` proves the equivalence.

## Implemented proof

The Library's representative congruence for the almost-everywhere
convergence and vanishing of the proper parabolic periods transfers the
full AE cusp condition between `φ` and `f`. In the forward direction,
`continuous_normalizedParabolicConstantTerm` proves continuity of the
constant term. Before descending in the radical variable, its integrand
is the continuous pullback along multiplication of the radical element
and the ambient point. The open quotient map in the radical variable
proves joint continuity after descent; compactness of the radical
quotient and its finite normalized measure allow continuity to pass
through the integral.

Restrict this continuous constant term to the norm-one subgroup. It is
the Library's positive quotient period there. The norm-one Haar measure
is positive on nonempty open sets, so the almost-everywhere zero period
is zero at every norm-one point. In
`positiveQuotientConstantTerm_normOneProjection`, the identity intertwining
right translations under the norm-one-to-positive quotient homeomorphism
compares the integrands pointwise. It identifies the constant term at
an arbitrary adelic point with the period at its norm-one projection.
Thus it vanishes everywhere. Conversely the published
`mem_aeParabolicCuspidalFunctionSubmodule_of_continuous` already proves
the almost-everywhere condition from pointwise cuspidality of `f`.

## Provenance and scope

This is a derived comparison for the Library's canonical measures. In
the `GL_n` summand realization route it formalizes the step of recovering
pointwise constant terms in Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 9.2.3, printed p. 243 (PDF p. 255), as used
in the proof of Theorem 9.7.3, (9.40), printed pp. 265–266 (PDF pp. 277–278).
The proof uses continuity on the actual compact radical quotients. It does
not construct continuous representatives from arbitrary classes, show
smoothness or finiteness of any representative, or prove density.
