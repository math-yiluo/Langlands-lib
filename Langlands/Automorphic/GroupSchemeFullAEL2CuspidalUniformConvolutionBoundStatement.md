# Uniform evaluation of smoothed cuspidal \(L^2\) vectors

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalUniformConvolutionBoundStatement`
is the uniform estimate for the original full cuspidal \(L^2\) action.
The group \(G\) is a connected reductive affine group scheme locally of
finite type over a number field \(F\). The family of radicals of proper
rational parabolics uses `ParabolicDynamicStatement`. A central morphism
\(i:T\to G\) has a supplied splitting \(T\simeq\mathbb G_m^I\) with \(I\)
finite, and its pullback on rational characters is injective with
finite-index image. Haar measure on the common character-norm kernel
\(G(\mathbb A_F)^1\) is assumed to be right invariant.

Let \(A_i\) be the image of the positive real coordinates of \(T\) at
the infinite places and \(Q=A_iG(F)\backslash G(\mathbb A_F)\).
The quotient measure is `positiveRationalQuotientHaarMeasure`, pushed
forward from \(G(F)\backslash G(\mathbb A_F)^1\) by inclusion. The
space \(S\) is `fullAEL2CuspidalSubmodule`, cut out by the separate
convergence and almost-everywhere vanishing of the normalized periods
for all proper rational parabolics. Each radical quotient measure has
mass one. The integrated operator \(R(f)\) uses full adelic `Measure.haar`
and the original right action on \(S\).

The weight \(f\) is a compactly supported continuous function on the full
adelic group with `IsAdelicTestFunction`. It has smooth infinite slices
and is invariant under left and right translation by open subgroups of
the finite adelic points. For each \(f\), the statement gives \(C_f\geq 0\)
such that for every \(\phi\in S\) the class \(R(f)\phi\) has a continuous
representative \(v\) satisfying

\[
  |v(q)|\leq C_f\|\phi\|_2 \qquad(q\in Q).
\]

The representative equality is almost everywhere for the quotient
measure. The constant depends on the weight and the fixed group and
measure data.

This is the full-group test-weight formulation of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), (9.13) in
Lemma 9.3.3, printed pp. 247–248 (PDF pp. 259–260), for the cuspidal
subspace in the number-field case. Their weights are on
\(A_G\backslash G(\mathbb A_F)\). When \(i\) is a split component,
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup` identifies
\(A_i\) with their \(A_G\), the image of the identity component of the
real points of the greatest \(\mathbb Q\)-split torus in
\(\operatorname{Res}_{F/\mathbb Q} Z_G\). The quotient convention is
§2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
(PDF pp. 85–86). On this quotient the full-group right action factors
through \(A_G\backslash G(\mathbb A_F)\), and integration in the
central variable gives the corresponding weight for the factored
action. Theorem 9.6.4, printed p. 264 (PDF p. 276), gives the rapid
decrease of smoothed cuspidal vectors used to obtain bounded evaluations.
