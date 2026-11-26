# Passage of Eisenstein series to a standard family with a compact in good position

Module `Langlands.Global.AdelicEisensteinStandardizationStatement`. It contains one statement, `Langlands.Global.EisensteinStandardizationStatement`, and no proof.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §2.1, pp. 189–190 (the fixed minimal parabolic, the standard parabolics and the maximal compact subgroup in good position); §2.2, p. 191 (the twist \(\varphi_\lambda\) and the series (2.1)).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995) (literature id `moeglin-waldspurger-1995-spectral-decomposition`): I.1.4, pp. 4–5 (maximal compact subgroups in good position).

Provenance: derived. Bernstein–Lapid work throughout with standard parabolics of one minimal parabolic and with one maximal compact subgroup in good position. The Library's `EisensteinSystemDominationStatement` (module `AdelicEisensteinSystemDominationStatement`) instead allows an arbitrary parabolic \(P\) with a root presentation and an arbitrary maximal compact \(K\) with \(P(\mathbb A)K=G(\mathbb A)\). Its Markdown, section "Changing the Iwasawa compact", describes how to pass from that setting to Bernstein–Lapid's. The statement here records the outcome of this passage for one inducing function.

## Statement

The binders are those of `EisensteinSystemDominationStatement`, without the positivity of the matrix size \(N\):

- a number field \(F\) and an affine group scheme \(G\) of finite type, connected reductive;
- a parabolic \(p:P\to G\) with unipotent radical `iU`, Levi `l`, split component `a` and root presentation `r`;
- a maximal compact subgroup \(K\) of \(G(\mathbb A)\) with `hK : IsIwasawaCompact p K`;
- a closed matrix embedding `rho`, the smooth structure `hsmooth` and a commutator datum `hcalc`;
- a function \(\varphi\) automorphic on \(U(\mathbb A)M(F)\backslash G(\mathbb A)\) for the archimedean part \(K_\infty\) of \(K\).

**Assertion.** There are:

- a standard parabolic family `fam` (module `AdelicLeadingCuspidalComponents`) and a standard index \(I\);
- a maximal compact subgroup \(K'\) of \(G(\mathbb A)\) with `hK' : IsIwasawaCompact (fam.p I) K'`;
- an archimedean point \(t\in G(F_\infty)\) (`InfiniteAdelicGroupPoints F G`), which acts on \(G(\mathbb A)\) through `ofInfinite F G t`, the point with archimedean component \(t\) and finite component \(1\);
- a complex linear isomorphism `iota` from \(X^*(P)\otimes\mathbb C\) to \(X^*(P_I)\otimes\mathbb C\), where \(P_I\) is `fam.P I`;
- finitely many functions \(\varphi'_0,\dots,\varphi'_{m-1}\) on \(G(\mathbb A)\) and complex linear forms \(\ell_0,\dots,\ell_{m-1}\) on \(X^*(P)\otimes\mathbb C\).

They have the following properties:

1. **The same parabolic.** `fam.p I` and \(p\) have the same image in \(G\) (`SubgroupFunctor.range`), and there is a morphism \(j:P_I\to P\) with \(p\circ j=\) `fam.p I`, that is `j ≫ p = fam.p I` (so \(j\) is the identification of the two subgroup schemes) such that `iota` is the restriction of characters along \(j\) (`parameterRestrict j`).
2. **Good position.** \(K'\) is in good position for `fam`: it is maximal compact, it satisfies Iwasawa coverage for the minimal standard parabolic `fam.p ⟨∅, _⟩`, and it meets every standard Levi \(M_J(\mathbb A)\) in a maximal compact subgroup.
3. **New inducing data.** Every \(\varphi'_i\) is automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) for the archimedean part \(K'_\infty\) of \(K'\) (`fam.IsAutomorphicOn`).
4. **Transport of automorphy.** If \(f\) is automorphic on \(G(F)\backslash G(\mathbb A)\) for \(K_\infty\), then \(g\mapsto f(gt)\) (right translation by `ofInfinite F G t`) is automorphic on \(G(F)\backslash G(\mathbb A)\) for \(K'_\infty\), with the same `hcalc` and `rho`.
5. **Transport of regularity.** Let `r'` be the presentation of \(P_I\) given by the family. For every \(R\) there is \(R'\) such that `iota` maps every \(R'\)-regular parameter for `r` to an \(R\)-regular parameter for `r'` (`IsRegularParameter`).
6. **Comparison of Eisenstein series.** There is \(R\) such that for every \(R\)-regular \(\lambda\) for `r` and every \(g\in G(\mathbb A)\),
   \[
   E_{P,K}(\varphi,\lambda)(gt)=\sum_{i<m}e^{\ell_i(\lambda)}\,E_{P_I,K'}\bigl(\varphi'_i,\iota(\lambda)\bigr)(g),
   \]
   where \(E_{P,K}\) is `hK.eisensteinSeries` and \(E_{P_I,K'}\) is `hK'.eisensteinSeries`.

Properties 5 and 6 use three instances for `fam` and \(I\): finiteness of the relative Weyl group, the closed immersion `fam.p I`, and the monomorphism property of the map `fam.f I` of split tori. They are quantified inside the conclusion. The Weyl group instance is a subsingleton and the other two are propositions, so any choice gives the same assertion.

## Why it holds

This explains the truth of the statement; the module contains no proof.

- **The standard family.** The presentation `r` provides a maximal split torus and a generic cocharacter, from which `StandardParabolicFamily.ofMaximalSplitTorus` (module `AdelicStandardParabolicFamilyConstruction`) builds a standard family. The subset of simple roots of `r` gives an index \(I\) whose parabolic `fam.p I` has the same image as \(p\). The published transport along parabolics with equal image (module `AdelicEisensteinParabolicRangeTransport`, for example `IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`) identifies the Eisenstein series, the twists and the parameter spaces. Regularity is transported as in `EisensteinRegularityParabolicTransportStatement` (module `AdelicEisensteinRegularityParabolicTransport`).
- **A compact in good position.** Mœglin–Waldspurger I.1.4 and Bernstein–Lapid §2.1 provide a maximal compact subgroup in good position with respect to the minimal parabolic of the family. The Library assembles such a subgroup from local ones (`standardLeviCompactAssembly`, module `AdelicStandardLeviCompactAssembly`). The archimedean factors exist by `infinitePlaceStandardLeviCompact`. The finite factors exist by `finitePlaceStandardLeviCompactReduction`, from `BruhatTitsAvailabilityStatement`.
- **The archimedean translate.** Maximal compact subgroups of \(G(F_\infty)\) are conjugate, so there is \(t\in G(F_\infty)\) with \(K'_\infty=tK_\infty t^{-1}\). For \(R_tf(g)=f(gt)\) and \(k'=tkt^{-1}\) one has \(R_tf(gk')=f(gtk)\), so right translation by \(t\) carries \(K_\infty\)-finite functions to \(K'_\infty\)-finite functions. It preserves left invariance under \(G(F)\), smoothness, the finite level (since \(t\) is archimedean) and moderate growth, and it commutes with the center of the enveloping algebra; compare `IsAutomorphicFunctionOn.infiniteRightTranslate` (module `GroupSchemeAutomorphicRightTranslation`). Put \(C=t^{-1}K't\). Its archimedean part is \(K_\infty\) and its finite part is that of \(K'\). By `IsIwasawaCompact.eisensteinSeries_mul_conjInv` (module `AdelicEisensteinConjugateCompactProof`), applied with \(C\) on the left, the series for \(C\) at \(gt\) is the series for \(K'\) of the translated inducing function \(x\mapsto\psi(xt)\) at \(g\), times the height power \(m_C(t)^\lambda=\exp\langle\lambda,H_C(t)\rangle\), which is the exponential of a linear form in \(\lambda\).
- **The finite height discrepancy.** \(K\) and \(C\) have the same archimedean projection. The published `EisensteinFiniteCompactChangeStatement` (module `AdelicEisensteinFiniteCompactChangeStatement`) writes \(\varphi_\lambda\) for \(K\) as a finite sum \(\sum_v e^{\langle\lambda,v\rangle}\) of twists for \(C\) of finitely many fixed automorphic functions. In the region of absolute convergence the Eisenstein series is linear in its inducing function, which gives the finite sum in property 6. The linear forms \(\ell_i\) collect \(\langle\cdot,v\rangle\) and \(\langle\cdot,H_C(t)\rangle\), transported through `iota`.

## Use

The statement reduces assertions about the regular Eisenstein series of an arbitrary \((P,K,\varphi)\) to assertions about finitely many Eisenstein series for a standard family and a compact in good position. Such statements include the conditions (6.21)–(6.22) and the cuspidal tests (8.2b) of Bernstein–Lapid. For example, `EisensteinCuspidalTestSystemStatement` (module `AdelicEisensteinCuspidalTestSystemStatement`) asserts uniqueness for automorphic forms for \(K_\infty\) and arbitrary \(K\), while the leading-component argument of Bernstein–Lapid §6 is stated for a compact in good position. Property 4 carries the automorphy hypothesis across, and property 6, with coefficients \(e^{\ell_i(\lambda)}\) entire in \(\lambda\), carries the conclusion back.
