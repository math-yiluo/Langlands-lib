# Twisted positive-quotient trace comparison

`Langlands.TraceFormula.positiveQuotientTwistedTraceComparison.{u}` proves
`Langlands.TraceFormula.PositiveQuotientTwistedTraceComparisonStatement.{u}`.
Write \(Q^+=A^+G(F)\backslash G(\mathbb A_F)\) and
\(Q^1=G(F)\backslash G(\mathbb A_F)^1\), with their Library quotient measures.

## Implemented proof

1. Functoriality `map_comp_apply` shows that the adelic map of an endomorphism
   fixing \(T\) fixes its positive image pointwise. The theorem
   `AdelicGroupPoints.rational_naturality` gives preservation of the rational
   subgroup. These two subgroups generate `positiveRationalSubgroup`. Applying
   the same argument to \(\tau^{-1}\), whose morphism also fixes \(T\), gives
   the membership equivalence that defines the quotient automorphism on \(Q^+\).
2. Write \(j:Q^1\to Q^+\) for `positiveQuotientMeasurableEquiv`. On a norm-one
   representative \(n\), the inverse quotient automorphisms on both sides of
   \(j\) use the same inverse adelic action. Consequently the inverse on
   \(Q^+\) equals \(j\circ\bar\theta^{-1}\circ j^{-1}\), where
   \(\bar\theta=\texttt{rationalQuotientAut}\). The two directions of \(j\)
   preserve the quotient measures by `measurePreserving_positiveQuotient`.
   The inverse \(\bar\theta^{-1}\) preserves the norm-one quotient measure by
   `measurePreserving_rationalQuotientAut_symm`, which uses finite order.
   Composition gives the measure-preservation witness on \(Q^+\).
3. `Lp.compMeasurePreservingₗᵢ` gives the pullback \(U:L^2(Q^+)\to L^2(Q^1)\).
   The composition and identity laws for `Lp.compMeasurePreserving` give its
   inverse as pullback along \(j^{-1}\). Since `twistOperator` pulls back along
   the inverse quotient automorphism, the coset identity from step 2 gives
   \(U I_\Theta=I_\theta U\) by the same composition law.
4. The integrated-action calculation follows the argument in
   `PositiveQuotientTraceComparisonProof`. The almost-everywhere formula for
   \(\pi(n)\) identifies it in `Lp` with pullback by norm-one right translation.
   The two right-translation definitions agree on representatives.
   `positiveQuotientHomeomorph_rightTranslate` then intertwines ambient
   translation by \(g\) with norm-one translation by \(p(g)\), where
   \(p=\texttt{normOneProjection}\). Under `normOneDecomposition`, a point
   \(g=a n\) has \(p(g)=n\). On each vector the proof commutes \(U\) with the
   Bochner integral, changes variables by `measurePreserving_normOneDecomposition`,
   and integrates the positive factor first by `integral_prod_symm`.
   The vector \(\pi(n)Uv\) is constant in that inner integral.
   `integral_smul_const` gives \(f^1(n)\pi(n)Uv\), proving \(UR(f)=\pi(f^1)U\).
5. The two intertwining identities give conjugacy of \(R(f)\circ I_\Theta\)
   and \(\pi(f^1)\circ I_\theta\). Bounded rectangular cyclicity
   (`operatorTraceCyclicity`) applied in both directions gives trace-class
   equivalence. Its trace identity and \(U^{-1}U=1\) give equality of traces
   under the trace-class condition.

## Source correspondence

Getz–Hahn §2.6, (2.19)–(2.22) and Lemma 2.6.2 (printed pp. 68–69, PDF
pp. 85–86), describe the norm-one group, the central quotient and the
right-equivariant coset homeomorphism for reductive groups over number fields.
Section 18.5 uses the fixed subgroup \(A_G^\theta\) in (18.31)–(18.32) and
defines the inverse pullback in (18.33) (printed p. 487, PDF p. 494).
Corollary 18.5.1 (printed p. 488, PDF p. 495) uses test functions on the
central quotient. When the positive split component realizes \(A_G\), the
pointwise fixation assumed here gives \(A_G^\theta=A_G\). The Lean comparison
is derived from this quotient description and twist convention. It implements
the averaging of an ambient test function with the Library's normalized
positive Haar measure and compares the resulting operators on the two
quotient spaces.
[J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, 2024](https://doi.org/10.1007/978-3-031-41153-3)
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
