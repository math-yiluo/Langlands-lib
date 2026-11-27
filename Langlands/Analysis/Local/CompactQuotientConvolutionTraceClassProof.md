# Trace-class convolution products on a compact left coset space

`Langlands.QuotientIntegration.compactQuotientConvolutionTraceClass`
proves `Langlands.QuotientIntegration.CompactQuotientConvolutionTraceClassStatement`
(module `Langlands.Analysis.Local.CompactQuotientConvolutionTraceClassStatement`).
It works with the data of the statement itself: the compatible measure
\(\nu\) on the compact left coset space \(H\backslash G\), the left invariant
measure \(\mu_G\) on \(G\), and the norm-preserving action \(\pi\) on
\(L^2(\nu)\) that acts almost everywhere by right translation. Write
\(R(f)\) for `integratedIsometricAction μG π _ _ f _`, the operator
\(\phi\mapsto\int_G f(g)\,\pi(g)\phi\,d\mu_G(g)\).

## The Lean proof

Let \(f_1,f_2\) be compactly supported continuous weights.

1. **Integrability of the factors.** A continuous function with compact
   support is integrable for a measure that is finite on compact sets
   (`Continuous.integrable_of_hasCompactSupport`), so \(f_1\) and \(f_2\)
   are \(\mu_G\)-integrable.

2. **The factors are Hilbert–Schmidt.** The published theorem
   `compactQuotientIntegratedHilbertSchmidt`
   (module `Langlands.Analysis.Local.CompactQuotientHilbertSchmidtProof`),
   applied to the same \(H\), \(\mu_H\), \(\mu_G\), \(\nu\), compactness
   hypothesis and action \(\pi\), states that \(R(f)\) is Hilbert–Schmidt
   for every compactly supported continuous \(f\). It applies to \(f_1\)
   and \(f_2\).

3. **The convolution identity.** The published theorem
   `Langlands.Analysis.integratedActionConvolution`
   (module `Langlands.Representation.Unitary.IntegratedConvolutionProof`),
   applied to the Hilbert space \(L^2(\nu)\), gives integrability of the
   left-measure convolution
   \[
   (f_1\star f_2)(g)=\int_G f_1(a)\,f_2(a^{-1}g)\,d\mu_G(a)
   \]
   together with the operator identity
   \(R(f_1\star f_2)=R(f_1)\circ R(f_2)\). Its hypotheses on \(G\) and
   \(\mu_G\) (measurable multiplication and inversion, s-finiteness and
   left invariance) are found by instance search: a measure finite on
   compact sets on a second countable locally compact space is
   σ-finite, and the Borel structure of a second countable topological
   group makes multiplication and inversion measurable.

4. **Trace class.** The integrability proof from step 3 is the witness of
   the existential. After rewriting with the operator identity, the
   published theorem
   `Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTraceClass`
   (module `Langlands.Analysis.HilbertSchmidtProductTraceClassProof`),
   applied with \(B=R(f_2)\) and \(C=R(f_1)\), shows that the composition
   \(C\circ B=R(f_1)\circ R(f_2)\) is trace class in the sense of
   `Langlands.Analysis.OperatorIdeals.IsTraceClass`.

The proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Correspondence with the source

The argument is the final paragraph of the proof of Lemma 9.3.3 in
J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*
(2024), printed pp. 247–248 (PDF pp. 259–260), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
There a smooth compactly supported \(f\) is written, by the
Dixmier–Malliavin lemma (Theorem 4.2.9, Exercise 9.8), as a finite linear
combination of convolutions \(f_1*f_2\); then \(R(f)\) is a finite linear
combination of products of two Hilbert–Schmidt operators and is of trace
class (Exercise 9.2).

The Lean proof carries out this step for a single convolution, with the
following differences from the source.

- The Lean proof works on the whole \(L^2(\nu)\) of a compact left coset
  space \(H\backslash G\), where \(G\) is a Hausdorff, second countable,
  locally compact group and \(H\) is a closed subgroup. Lemma 9.3.3 works
  on a closed \(A_G\backslash G(\mathbb{A}_F)\)-invariant subspace \(V\) of
  \(L^2([G])\) for an adelic quotient \([G]\) of finite volume over a
  global field \(F\). The source does not assume \(G\) reductive there
  (§9.3, printed p. 246, PDF p. 258); it notes that reductivity of \(G\)
  is a sufficient condition for finite volume (printed p. 248, PDF
  p. 260, citing its Theorem 2.6.3).
- The Hilbert–Schmidt property of the factors comes from compactness of
  \(H\backslash G\) through `compactQuotientIntegratedHilbertSchmidt`,
  instead of from the estimate (9.13) of the lemma.
- The weights are compactly supported and continuous, with no smoothness
  needed, since no Dixmier–Malliavin factorization is performed.
- The convolution is formed with the left invariant measure \(\mu_G\), as
  in `IntegratedActionConvolutionStatement`; formula (3.9) of the source
  uses a right Haar measure.

The passage from single convolutions to finite sums of them and to smooth
weights is carried out in the module
`Langlands.Analysis.Local.CompactQuotientSmoothTraceClassReduction`
(`compactQuotientSmoothTraceClass_of_convolution` and
`compactQuotientProductSmoothTraceClass_of_convolution`), which takes this
statement as a hypothesis.
