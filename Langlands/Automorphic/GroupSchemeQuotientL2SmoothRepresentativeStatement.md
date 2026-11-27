# Smooth representatives of adelic quotient convolution

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeQuotientL2SmoothRepresentativeStatement`
is stated for an affine, locally finite type group scheme \(G\) over a
number field \(F\), with a witness of `SmoothOfRelativeDimension` giving
the infinite adelic atlas. It takes a central morphism \(i:T\to G\) with a
supplied splitting \(T\simeq\mathbb G_m^I\) for a finite set \(I\).
The pullback \(i^*:X_F^*(G)\to X_F^*(T)\) on rational characters is
injective with finite-index image. The Haar measure on \(G(\mathbb A_F)^1\),
the common kernel of the rational character norms, is assumed to be
right invariant.

The image \(A_i\) of the positive real coordinates of \(T\), embedded
diagonally at the infinite places, gives the left quotient
\(A_iG(F)\backslash G(\mathbb A_F)\). The \(L^2\) and almost-everywhere
measure `positiveRationalQuotientHaarMeasure` is the pushforward of the
Library's norm-one rational quotient Haar measure along the
inclusion-induced homeomorphism. Write \(da\) for `Measure.haar` on the
full adelic group, used in both scalar convolution and
`haarQuotientL2IntegratedAction`.

For an input \(L^2\) class \(\phi\), its chosen measurable representative
pulls back to a locally integrable function \(\Phi\) on the full adelic
group. An `IsAdelicTestFunction` weight \(f\) is continuous, has smooth
infinite slices and compact support, and is fixed under left and right
translation by open subgroups of the finite adelic points, possibly
different. The pointwise convolution \(\psi(x)=\int f(a)\Phi(xa)\,da\)
is adelically smooth. It is continuous, has smooth infinite slices, and
is fixed under right translation by one open subgroup of the finite
adelic points. It descends to a continuous quotient function representing
the integrated class almost everywhere for the quotient measure.

For each word of archimedean directions, the corresponding orbit
derivative of \(\psi\) is the convolution of \(\Phi\) by the iterated
kernel derivative. At one step the kernel derivative in direction \(X\)
acts on \(t\mapsto f(t^{-1}a)\) at the identity, with \(t\) embedded from
the infinite adelic group. Each iterated kernel is a smooth adelic test
function supported in the original topological support. The word order
is the order of `adelicIteratedDirectionalValue`.

This is the pointwise smoothing and differentiation step of
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*
(1995), I.2.5 Lemma (b) and its proof, printed p. 27 (PDF p. 10 in
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`). Their
square-integrable space has a unitary central character. The proposition
uses the Library's positive rational quotient and its full adelic test
weights. Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86),
supplies the quotient convention when \(G\) is connected reductive and
\(i\) is a split component. The Library then identifies \(A_i\) with
the canonical \(A_G\) from (2.20) by
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup`.
The smooth representative is used in the
cuspidal rapid-decay application of their Theorem 9.6.4, printed p. 264
(PDF p. 276).
