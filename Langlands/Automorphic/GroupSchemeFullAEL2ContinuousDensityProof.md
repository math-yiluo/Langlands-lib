# Density of continuous cuspidal classes by compact convolution

The theorem `groupSchemeFullAEL2ContinuousDensity` in this module proves
`GroupSchemeFullAEL2ContinuousDensityStatement`. Fix a closed complex
subspace \(P\) of the full almost-everywhere cusp space \(S\) that is
invariant under the adelic right action. Every \(\varphi \in P\) is then
the norm limit, inside \(P\), of vectors in the range of
`positiveParabolicCuspidalL2ToFullAE`.

## The implemented proof

1. **Approximating weights.** `groupSchemeFullAEL2HermitianApproximation`
   supplies real weights \(f_n\) on the adelic points. Each \(f_n\) is
   continuous, compactly supported and nonnegative. It has integral one
   for the inverse \(\mu_G^{-1}\) of the Haar measure \(\mu_G\), and
   satisfies \(f_n(a) = \Delta(a^{-1}) f_n(a^{-1})\). Their supports
   shrink to the identity. The integrated operators of the right action
   on \(S\), taken with respect to \(\mu_G^{-1}\), tend strongly to the
   identity. The proof regards \(f_n\) as complex-valued
   compactly supported continuous functions \(w_n\).

2. **Changing the measure.** The hypothesis that Haar measure on the
   norm-one group is right invariant gives right invariance of
   \(\mu_G\) (`ambientHaar_isMulRightInvariant`).
   `ConstantTermAverage.isInvInvariant_of_isMulRightInvariant` then gives
   inversion invariance, so \(\mu_G^{-1} = \mu_G\). Hence the operators
   \(B_n\) = `fullAEL2CuspidalIntegratedAction` with weight \(w_n\) and
   measure \(\mu_G\) are the operators of step 1, and
   \(B_n\psi \to \psi\) for every \(\psi \in S\).

3. **Staying in \(P\).** `integratedIsometricNaturality`, applied to the
   bounded right action on \(S\), uses its norm preservation
   (`norm_fullAEL2CuspidalBoundedRightAction`) and orbit measurability
   (`fullAEL2CuspidalOrbit_aestronglyMeasurable`). It shows that each
   \(B_n\) maps the closed invariant subspace \(P\) into itself. For
   \(\varphi \in P\) the vectors \(B_n\varphi\) therefore lie in \(P\) and
   converge to \(\varphi\) in the subspace topology of \(P\).

4. **Continuous cuspidal representatives.**
   `groupSchemeQuotientL2ContinuousRepresentative`, applied to the weight
   \(w_n\) and the class of \(\varphi\), gives a continuous function \(g\)
   on the positive rational quotient. It is almost everywhere equal to the
   integrated quotient action of \(w_n\) on that class. By
   `fullAEL2CuspidalIntegratedAction_val`, that integrated class is the
   class of \(B_n\varphi\). Since \(B_n\varphi\) lies in \(S\), the forward
   direction of `groupSchemeFullAEL2ContinuousCuspidality` puts the
   pullback of \(g\) in `normalizedParabolicCuspidalSubrepresentation`. So
   the mass-one constant term of \(g\) along every proper rational
   parabolic vanishes at every adelic point. Almost-everywhere equality
   makes \(g\) square integrable. Thus \(g\) is an element of the source of
   `positiveParabolicCuspidalL2ToFullAE`, and
   `coeFn_positiveParabolicCuspidalL2ToLp` identifies its image with
   \(B_n\varphi\).

5. **Conclusion.** Every term of the convergent sequence
   \((B_n\varphi)\) in \(P\) lies in the asserted set. Hence
   `mem_closure_of_tendsto` puts \(\varphi\) in its closure.

The quantitative bound in `groupSchemeQuotientL2ContinuousRepresentative`
is not used: only the continuous representative and its almost-everywhere
equality enter the proof.

## Source correspondence

The argument follows J. R. Getz and H. Hahn, *An Introduction to
Automorphic Representations* (2024), source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`:

- Steps 1–2 correspond to the Dirac sequences of §9.3, printed p. 246
  (PDF p. 258). Their conditions (a)–(c) are shrinking supports, the
  symmetry \(f_n(x) = f_n(x^{-1})\delta_G^{-1}(x)\) and total mass one,
  and the text states \(R(f_n)\varphi \to \varphi\). The Library's weights
  are continuous and compactly supported on the adelic points rather than
  smooth on \(A_G\backslash G(\mathbb{A}_F)\); smoothness is not needed
  for this argument.
- Step 3 is the remark in the proof of Lemma 9.3.1, printed p. 247
  (PDF p. 259), that closed invariant subspaces are invariant under the
  convolution operators.
- Step 4 corresponds to the pointwise evaluations
  \(x \mapsto R(f)\varphi(x)\) of Lemma 9.3.3 and (9.13), printed
  pp. 247–248 (PDF pp. 259–260). It also uses the vanishing of the
  constant-term periods \(P_\chi(R(g)\varphi)\) of §9.2, printed
  pp. 242–245 (PDF pp. 254–257), with \(H = N_P\) and trivial \(\chi\).
  For a continuous representative, almost-everywhere vanishing of these
  periods becomes vanishing at every point.

The density concerns continuous functions only. The comparison with
smooth vectors, finite vectors and growth conditions in Getz–Hahn
Theorem 9.7.3 is not part of this module.
