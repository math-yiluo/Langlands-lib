# Smooth representatives of adelic quotient convolution

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2SmoothRepresentative`
proves `GroupSchemeQuotientL2SmoothRepresentativeStatement`. Write
\(q:G(\mathbb A_F)\to A_iG(F)\backslash G(\mathbb A_F)\) for the quotient map,
\(\Phi=\phi\circ q\) for the pullback of the chosen representative of the
\(L^2\) input, and \(da\) for the Library's full adelic Haar measure.

Composing the strongly measurable representative with the continuous
Borel quotient map makes \(\Phi\) measurable.
`locallyIntegrable_positiveQuotientLpPullback` gives integrability on
compact sets. It applies pointwise kernel integrability at the identity
to a compactly supported continuous cutoff equal to one on the compact
set. With these two inputs, `adelicRightConvolutionDifferentiation` proves
that \(\psi(x)=\int f(a)\Phi(xa)\,da\) is continuous, smooth on each
archimedean slice, and right invariant under an open finite adelic subgroup.

In the one-step derivative formula, \(D_X\) differentiates the right
orbit of \(\psi\) at the identity in direction \(X\). On the kernel,
\(K_X f\) differentiates \(t\mapsto f(t^{-1}a)\) there, with \(t\)
embedded from the infinite adelic group. The inverse arises from the
left Haar change of variables \(a\mapsto ta\) in \(\psi(xt)\).
The proof inducts on the derivative word. The empty word has kernel \(f\).
For \(X::s\), it substitutes the formula for \(D_s\psi\) and uses
`adelicDirectionalValue_pair` to apply the one-step formula on each
finite slice. The kernel is \(K_X k_s\), where \(k_s\) is the kernel for
the tail \(s\), so both derivative words use the same right fold.
`rightConvolutionKernelDerivative_isTestFunction` preserves the test
function conditions and gives
\(\operatorname{tsupp}(K_X k_s)\subseteq\operatorname{tsupp}(k_s)\).
Transitivity gives support inclusion in \(\operatorname{tsupp}(f)\).

`positiveQuotientLpSmoothing_invariant` gives \(\psi(\gamma x)=\psi(x)\)
for \(\gamma\in A_iG(F)\), since \(q(\gamma xa)=q(xa)\). The proof
uses `LeftCosetSpace.lift` and its continuity theorem to descend \(\psi\).
`positiveQuotientLpSmoothing_ae_eq` identifies this descended function
almost everywhere with `haarQuotientL2IntegratedAction` for the original
`positiveRationalQuotientHaarMeasure` and \(da\).

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.5 Lemma (b) and its proof, printed p. 27, give the smoothing and
left-translation derivative on the kernel for square-integrable inputs
with a unitary central character. The Lean proof implements this
analytic step for the positive rational quotient using the full-group
convolution above. The retained chapter file is
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, PDF p. 10,
registered as `moeglin-waldspurger-1995-growth-and-constant-terms`
(SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`).

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
(2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86),
give the norm-one quotient and its identification with \([G]\) in the
connected reductive number-field setting. With a split component,
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup` identifies
the Library's \(A_i\) with \(A_G\). Theorem 9.6.4, printed p. 264
(PDF p. 276), uses the smoothed cuspidal function in a rapid-decay
application. The retained book is registered as
`getz-hahn-2024-automorphic-representations`
(SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
