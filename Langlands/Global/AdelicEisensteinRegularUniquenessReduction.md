# Uniqueness of convergent Eisenstein series from five premises

Module `Langlands.Global.AdelicEisensteinRegularUniquenessReduction`. It states the implication `Langlands.Global.EisensteinRegularUniquenessReductionStatement` and proves it as `Langlands.Global.eisensteinRegularUniqueness_of`. The five premises are not proved here; the module does not prove `EisensteinRegularUniquenessStatement` itself.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): Theorem 6.3 and the leading cuspidal components (6.11), §6.3, p. 203; §6.10, (6.17)–(6.22) and Corollary 6.10, pp. 207–209; the use of (6.21)–(6.22) in the proof of Proposition 8.4, §8.4, pp. 223–224.
- The same paper, Theorem 2.3 (1), p. 191, with §2.2, p. 191, for the automorphy of convergent Eisenstein series and of the twists \(\varphi_\lambda\).

Provenance: derived. Bernstein–Lapid assert (6.22) after (6.21) and use it in §8.4; their reason is the comparison of leading cuspidal components through Corollary 6.10, Lemma 6.8 and Theorem 6.3. The implication here isolates the inputs of that comparison as five Library propositions and carries out the comparison.

## Statement

`EisensteinRegularUniquenessReductionStatement` is the implication, at one universe `u`,

```
LeadingCuspidalInjectivityStatement →
CuspidalProjectionDecompositionStatement →
EisensteinUniformCuspidalExpansionStatement →
ParameterTwistAutomorphyStatement →
EisensteinRegularAutomorphyStatement →
EisensteinRegularUniquenessStatement
```

The premises are, in this order:

1. `LeadingCuspidalInjectivityStatement` (module `AdelicLeadingCuspidalInjectivityStatement`): Bernstein–Lapid Theorem 6.3, two automorphic forms on \(G(F)\backslash G(\mathbb A)\) with a common family of leading cuspidal components are equal.
2. `CuspidalProjectionDecompositionStatement` (module `AdelicCuspidalProjectionDecompositionStatement`): for `Q ≤ P` and `φ` automorphic on \(U_P(\mathbb A)M_P(F)\backslash G(\mathbb A)\), the constant term \(C_Q\varphi\) has a unique cuspidal projection, and it has an exponent decomposition.
3. `EisensteinUniformCuspidalExpansionStatement` (module `AdelicEisensteinUniformCuspidalExpansionStatement`): Corollary 6.10 for finite families, in the norm-one Levi cusp tests.
4. `ParameterTwistAutomorphyStatement` (module `AdelicParameterTwistAutomorphyStatement`): \(\varphi_\lambda\) is automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) with \(\varphi\).
5. `EisensteinRegularAutomorphyStatement` (module `AdelicEisensteinRegularAutomorphyStatement`): Bernstein–Lapid Theorem 2.3 (1) in the region of absolute convergence, for the same standard family and compact as the conclusion: for sufficiently regular \(\lambda\) the Eisenstein series \(E(\varphi,\lambda)\) of an automorphic \(\varphi\) on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) is automorphic on \(G(F)\backslash G(\mathbb A)\).

The conclusion is `EisensteinRegularUniquenessStatement` (module `AdelicEisensteinRegularUniquenessStatement`), unchanged.

## Proof

The proof of `eisensteinRegularUniqueness_of` follows the "Why it holds" section of `AdelicEisensteinRegularUniquenessStatement.md`. Fix the data of the conclusion: `fam`, `I`, `K`, `rho`, the inducing functions `φ i` (`i < n`) and the competing data `data J`.

**Choice of the threshold.** The standard indices form a finite type (subsets of the finite set of simple roots). Premise 3, applied to the family `φ` and to each standard `J`, gives a threshold `Rexp J`, competing data `dataE J : CompetingWeylExponents fam I J 1` and a degree bound. Premise 5, applied to each `φ i`, gives a threshold `Raut i`. Let `S` be the finite set of the shifts `chamberEmbedding J (Re (offset k))` of all labels of `data J` and of `dataE J`, over all `J`. The lemma `exists_regular_forall_not_isLeadingExponent` (below) gives a threshold `Rsep` for `S`. The proof takes
\[
R=\max\Bigl(R_{\mathrm{sep}},\ \textstyle\sum_i|R_{\mathrm{aut},i}|+\sum_J|R_{\mathrm{exp},J}|\Bigr),
\]
which depends neither on \(\lambda\) nor on the coefficients \(a_i\). Regularity is monotone in the threshold, so an \(R\)-regular \(\lambda\) is regular for each of these thresholds.

**The two automorphic forms.** Fix an \(R\)-regular \(\lambda\), coefficients \(a_i\) and an automorphic \(v\) satisfying the hypothesis. Put \(E=\sum_ia_iE(\varphi_i,\lambda)\) and \(\varphi_\lambda=\sum_ia_i\varphi_{i,\lambda}\). By premise 5 and the submodule `automorphicFunctionsOn`, \(E\) is automorphic on \(G(F)\backslash G(\mathbb A)\); by premise 4, \(\varphi_\lambda\) is automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\). By `isAutomorphicOn_top_iff` (module `AdelicStandardTopAutomorphy`), \(v\) and \(E\) are automorphic for the top index, so premise 2 applies to them along every `J`.

**Along one standard `J`** (`exists_nonleading_difference_of_cuspidal_conditions`). Let \(X=C_{I,J}\varphi_\lambda\) (`parabolicConstantTerm`). If \(J\le I\), premise 2 for \(\varphi_\lambda\) gives a cuspidal projection \(\psi_\varphi\) of \(X=C_J\varphi_\lambda\) with an exponent decomposition; otherwise \(X=0\) and \(\psi_\varphi=0\) (`isCuspidalProjection_zero`). Premise 2 gives the cuspidal projections \(\psi_v\) of \(C_Jv\) and \(\psi_E\) of \(C_JE\), with exponent decompositions, and the uniqueness of \(\psi_v\).

1. *The solution.* The hypothesis gives a cuspidal projection \(v_c\) of \(C_Jv-X\) with a decomposition \(\sum_{\mu\in s}c_\mu\) whose nonzero components carry labels of `data J`. Cuspidal projections add (`isCuspidalProjection_add`), so \(\psi_\varphi+v_c\) is a cuspidal projection of \(C_Jv\), and \(\psi_v=\psi_\varphi+v_c\) by uniqueness.
2. *The Eisenstein series.* Write \(\psi_E-\psi_\varphi=\sum_{\mu\in t}d_\mu\) over the union \(t\) of the two exponent sets, with \(d_\mu\) the difference of the components padded by zero. Each \(d_\mu\) is cuspidal and automorphic on \(U_J(\mathbb A)M_J(F)\backslash G(\mathbb A)\) with unnormalized exponent \(\mu\). Premise 3 gives terms with exponents the labels of `dataE J`, whose cusp tests are those of \(C_JE-X\), hence those of \(\psi_E-\psi_\varphi\). By `leviPairing_eq_zero_of_sum_leviPairing_eq` every \(d_\mu\) with \(\mu\) none of these labels has vanishing cusp tests, so it is \(0\) by `eq_zero_of_isCuspidalAlong_of_forall_leviPairing_eq_zero`. Thus \(\psi_E-\psi_\varphi\) is a sum of components with labels of `dataE J`.
3. *Comparison.* Hence \(\psi_v=\psi_E+\sum_{\mu\in u}e_\mu\), where every \(e_\mu\) has unnormalized exponent \(\mu\), and every \(\mu\in u\) is a label of `data J` or of `dataE J`. By `CompetingWeylExponents.chamberEmbedding_label` and the field `ambient`, the embedded real part of such a label is \(w_k(\operatorname{Re}\lambda)\) plus a shift in `S`, with \(w_k\neq1\) keeping the simple roots of \(I\) positive (fields `competing`, `positive`). So no such label is leading.

**Conclusion.** The published `exists_common_leadingComponents_of_nonleading_differences` (module `AdelicLeadingExponentDirectness`) gives a common family of leading cuspidal components of \(v\) and \(E\), and premise 1 gives \(v=E\).

## Auxiliary results

In namespace `Langlands.Global.StandardParabolicFamily`:

- **Pairings.** `leviPairingIntegrand_add_fun`, `leviPairingIntegrand_sub_fun`, `leviPairingIntegrand_sum_fun` (the integrand is linear in the function) and `leviPairing_add_of_integrable`, `leviPairing_sub_of_integrable`, `leviPairing_sum_of_integrable` (linearity of the pairing for absolutely convergent integrands).
- **Projections.** `isAutomorphicOn_add_of_isAutomorphicOn`, `isAutomorphicOn_sub_of_isAutomorphicOn` (from the submodule `automorphicFunctionsOn`), `isCuspidalAlong_add_of_isAutomorphicOn` (through the published `constantTermLinear`), `isCuspidalProjection_add` and `isCuspidalProjection_zero`.
- **Localization.** `iSupIndep_unnormalizedCharacterEigenspace`: the joint generalized eigenspaces of the characters \(b\mapsto b^\lambda\) of the positive split component \(\mathfrak A_J\), acting by left translation, are independent; the characters are pairwise distinct by the published `eisensteinPositiveParameters`. `leviPairing_eq_zero_of_sum_leviPairing_eq`: fix a test \(\psi\); let \(d_\mu\) (\(\mu\in t\)) and terms \(f_k\) have unnormalized exponents \(\mu\) and \(\ell_k\) and absolutely convergent pairings with \(\psi\) at every point, and let \(\sum_\mu\langle d_\mu,\psi\rangle_g=\sum_k\langle f_k,\psi\rangle_g\) for all \(g\). Then \(\langle d_\mu,\psi\rangle_g=0\) for every \(\mu\in t\) that is no \(\ell_k\). *Proof.* By the published `leviPairingLinear_mem_jointGenEigenspace`, \(g\mapsto\langle d_\mu,\psi\rangle_g\) lies in the eigenspace of \(\mu\) and \(g\mapsto\langle f_k,\psi\rangle_g\) in that of \(\ell_k\). Group the terms by exponent; the grouped differences sum to zero, so each vanishes by independence. For \(\mu\) none of the \(\ell_k\), the group contains no term.
- **Detection.** These take `CuspidalProjectionDecompositionStatement` as the explicit hypothesis `hproj`, with \(K\) in good position. `integrable_leviPairingIntegrand_of_isAutomorphicOn`: an automorphic function on \(U_J(\mathbb A)M_J(F)\backslash G(\mathbb A)\) is its own constant term along \(J\) (`constantTerm_eq_self_of_automorphicOn`), and the projection supplied by `hproj` records the absolute convergence of its pairings with Levi cusp forms. `eq_zero_of_isCuspidalAlong_of_forall_leviPairing_eq_zero`: a cuspidal automorphic function on that quotient with vanishing cusp tests is zero, since it and \(0\) are both cuspidal projections of its own constant term and `hproj` gives uniqueness.
- **Nonleading labels.** `exists_regular_forall_not_isLeadingExponent`: for a finite set \(S\) of shifts there is \(R\) such that for every \(R\)-regular \(\lambda\), every \(w\neq1\) keeping the simple roots of \(I\) positive, every \(J\) and every exponent along \(J\) whose embedded real part is \(w(\operatorname{Re}\lambda)\) plus a shift in \(S\), the exponent is not leading. *Proof.* The embedded real part of \(\lambda\) is the lift of its restriction to \(A_I\) (published `eisensteinAmbientParameterLift`). The published `exists_regular_bound_for_ambient_chamber_separation` gives a simple root \(\beta\) with negative Weyl-invariant pairing, and `RelativeRootReflectionData.coroot_nonneg_iff` turns a nonnegative coroot pairing into a nonnegative form pairing. This is the identity-Weyl case of the published `eisensteinNonleadingWeylTerms`. `CompetingWeylExponents.chamberEmbedding_label` (namespace `Langlands.Global`) computes the embedded real part of a label from the field `ambient`.

The proof uses the axioms `propext`, `Classical.choice` and `Quot.sound` only.
