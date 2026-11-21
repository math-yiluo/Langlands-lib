# Center stability of the solutions of Ξ_main, from the Ad-invariance of the center

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), proof of Lemma 8.1 (§8.1, pp. 221–222), with the system Ξ_main of §7.2 (p. 211). In the proof of the "if" direction BL write "Clearly, \(V\) is \(\mathfrak z\)-invariant". This module proves that sentence for the Library's solution sets of Ξ_main.

The module proves `LocalFinitenessCenterStabilityStatement` (module `AdelicLocalFinitenessCenterStabilityStatement`) **conditionally**, from one premise:

- `hAd : AdelicEnvelopingCenterConjugationStatement` (module `GroupSchemeEnvelopingCenterConjugationStatement`): for connected reductive \(G\), every \(\mathrm{Ad}(k)\), \(k\in G(F_\infty)\), fixes the center of the complex enveloping algebra pointwise.

Everything else is proved here: differentiation under the convolution integral and under the constant-term integral, and compactness of the adelic quotients of the standard unipotent radicals.

## Main theorem `Langlands.Global.localFinitenessCenterStability_of`

Fix the data of the statement, a solution \(v\in\mathfrak F^R_L\) of Ξ_main\((s)\) with underlying carrier element \(f\), and a central \(Y\). The witness is \(w=\) `UniformGrowthFrechetSpace.envelopingActionCLM … Y v`, the published continuous operator of \(Y\) on \(\mathfrak F^R_L\). Its carrier element is `adelicCenterAction Y f` by definition (`rfl`). The three groups of equations of Ξ_main\((s)\) for \(Yf\) are:

1. **Harish-Chandra equations** \(\sum_k b_{i,k}(s)\,\delta(h_{i,k})(Yf)=c_i(s)\,Yf\): `rightConvolution_actualAdelicEnvelopingAction_of_conjugation`. Its inputs are the equation for \(f\), continuity and compact support of the test functions \(h_{i,k}\) (admissibility), and \(\mathrm{Ad}(k)Y=Y\) for all \(k\) (premise `hAd`).
2. **Constant-term equations** \(D_\alpha(s)(a_\alpha)\,C_{U_\alpha}(Yf)=0\): `isTranslationPolynomialSolution_subgroupConstantTerm_enveloping`. It needs compactness of \([U_\alpha]\). The group data identify the range of \(u_\alpha\) with the standard unipotent subgroup \(U_{\Delta_0\setminus\{\alpha\}}\), and `AdelicSubgroupPoints.compactSpace_rationalQuotient_standardUnipotent` gives compactness.
3. **Central equations** \(D_j(s)(z_j)(Yf)=0\): `isTranslationPolynomialSolution_actualAdelicEnvelopingAction`.

Only item 1 uses `hAd`. Items 2 and 3 hold for every element \(Y\) of the enveloping algebra, central or not.

## Lie-theoretic preliminaries

- `Langlands.Geometry.Manifold.continuous_groupTangentConjugation`: for a real Lie group modelled on a normed space \(E\), \(g\mapsto\mathrm{Ad}(g)=T_1(h\mapsto ghg^{-1})\) is continuous into \(E\to_L E\). The proof uses smoothness of the tangent map of \((x,h)\mapsto xhx^{-1}\) in tangent coordinates (`ContMDiffAt.mfderiv`). It then removes the trivialization at \(1\) by composing with the trivialization maps on both sides.
- `continuous_adelicTangentConjugation_apply`: \(k\mapsto\mathrm{Ad}(k)X\) is continuous on \(G(F_\infty)\).
- `adelicEnvelopingConjugation_expansion`: for every \(a\) in the enveloping algebra there are finitely many fixed \(e_i\) and continuous \(c_i\) on \(G(F_\infty)\) with \(\mathrm{Ad}(k)a=\sum_i c_i(k)\,e_i\). The proof is by induction over the tensor algebra. A generator \(z\otimes X\) is expanded in a real basis of the Lie algebra with the coordinates of \(\mathrm{Ad}(k)X\). Products use the product index set, and sums use the disjoint union.

## Derivatives along curves

- `hasDerivAt_evaluate_mul_curve` (a public copy of a private lemma of `GroupSchemeConstantTermEnvelopingProof`): along an integral curve \(c\) of the left-invariant field of \(X\), \(\frac{d}{dt}f(x\,c(t))=(Xf)(x\,c(t))\).
- `exists_differentialCurve`: for each real \(X\) there are a curve \(c\) with \(c(0)=1\) and \(\varepsilon>0\) such that \(c\) is continuous on \([-\varepsilon,\varepsilon]\) and the identity above holds for all \(f\), all \(x\) and all \(|t|<\varepsilon\). The curve is the local integral curve from `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`.
- `actualAdelicEnvelopingAction_mem_of_differential`: a complex subspace of the carrier that is stable under every real directional derivative is stable under the whole enveloping algebra. The proof inducts over the tensor algebra and uses `actualAdelicEnvelopingAction_generator`.

## Difference equations (central and constant-term equations)

- `translationPolynomialSubmodule a D`: the solutions \(\varphi\) of \(\sum_k D_k\,\varphi(a^kg)=0\) form a complex subspace.
- `isTranslationPolynomialSolution_enveloping_of_hasDerivAt`: let \(\Lambda\) be complex-linear from the carrier to functions on \(G(\mathbb A)\), and suppose that for each \(X\) and \(f\) some curve through \(1\) satisfies \(\frac{d}{dt}\big|_0\Lambda f(x\,c(t))=\Lambda(Xf)(x)\). If \(\Lambda f\) solves \(D(a)\varphi=0\), so does \(\Lambda(bf)\) for every \(b\). The subspace \(\Lambda^{-1}(\text{solutions})\) is stable under each \(X\): the function \(t\mapsto\sum_kD_k\,\Lambda h(a^kg\,c(t))\) vanishes identically, because the difference equation acts by left translation and the curve by right translation. Its derivative at \(0\) is therefore \(0\), and that derivative is the equation for \(\Lambda(Xh)\). The previous item then applies.
- `isTranslationPolynomialSolution_actualAdelicEnvelopingAction`: the case \(\Lambda=\) evaluation (the Library's `finitePlotSmoothEvaluation`).
- `continuous_subgroupConstantTermIntegrand_uncurry` (a public copy of a private lemma of `GroupSchemeConstantTermEnvelopingProof`): the constant-term integrand is jointly continuous.
- `hasDerivAt_constantTerm`: on a compact quotient \([U]\) with a finite measure, \(\frac{d}{dt}\big|_0 C_U f(x\,c(t))=C_U(Xf)(x)\). This is differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The derivative integrand is bounded by its maximum on the compact set \([-\varepsilon,\varepsilon]\times[U]\).
- `isTranslationPolynomialSolution_subgroupConstantTerm_enveloping`: let \(j:H\to G\) be a closed subgroup with compact \([\operatorname{range} j]\). Then the constant-term equations pass from \(f\) to \(bf\). This uses the previous items with \(\Lambda=\) the continuous constant term against the normalized quotient measure (`subgroupConstantTerm_eq_continuousConstantTerm`).

## Harish-Chandra equations

- `actualAdelicEnvelopingAction_finitePlotSmoothRightAction` (covariance): \(a\,(R(g)f)=R(g)\big(\mathrm{Ad}(g_\infty^{-1})a\,f\big)\). Write \(g=g_\infty g_f\). The finite part commutes with the enveloping action (`finitePlotSmoothEnvelopingAction_finiteRightAction`), and the infinite part is the Library's `finitePlotSmoothRightAction_actualAdelicEnvelopingAction`.
- `envelopingTranslate f a g y` \(=\Psi_a(g,y)=(a\,R(g)f)(y)\), with additivity and homogeneity in \(a\) (`envelopingTranslate_add`, `_smul`, `_zero`, and the same for evaluation of \(af\)).
- `continuous_envelopingTranslate`: \(\Psi_a\) is jointly continuous on \(G(\mathbb A)\times G(\mathbb A)\). By covariance and the expansion, \(\Psi_a(g,y)=\sum_i c_i(g_\infty^{-1})\,(e_if)(yg)\). This is a finite sum of products of continuous functions.
- `hasDerivAt_integral_mul_of_continuous`: for \(h\) continuous with compact support, jointly continuous \(\Psi,\Psi'\), a curve \(z\) continuous on \([-\varepsilon,\varepsilon]\), and \(\partial_t\Psi(g,z(t))=\Psi'(g,z(t))\) for \(|t|<\varepsilon\): \(\frac{d}{dt}\big|_0\int h(g)\Psi(g,z(t))\,dg=\int h(g)\Psi'(g,z(0))\,dg\). The bound is \(|h(g)|\cdot\max|\Psi'|\) on \([-\varepsilon,\varepsilon]\times\operatorname{tsupp}h\).
- `harishChandra_differential_step`: suppose \(a'\) acts as \(X\circ a\) and \(\sum_kb_k\int h_k(g)\Psi_a(g,y)\,dg=c\,(af)(y)\) for all \(y\). Then the same holds for \(a'\). Both sides are evaluated at \(y=x\,c(t)\) and differentiated at \(t=0\). The left side by the previous item: \(\partial_t\Psi_a(g,x\,c(t))=\Psi_{a'}(g,x\,c(t))\) by `exists_differentialCurve` applied to \(a\,R(g)f\). The right side by `exists_differentialCurve` applied to \(af\). Uniqueness of derivatives gives the identity for \(a'\).
- `harishChandra_actualAdelicEnvelopingAction`: the identity \(\sum_kb_k\int h_k(g)\,(a\,R(g)f)(x)\,dg=c\,(af)(x)\) holds for every \(a\), given the Harish-Chandra equation of \(f\). The elements \(a\) satisfying the identity form a submodule \(A\), since the integrands are integrable (continuous with compact support). The identity holds for \(a=1\): it is the equation of \(f\). The submodule is stable under left multiplication by the generators \(1\otimes X\) (previous item), hence by induction over the tensor algebra under left multiplication by everything. So \(A\) contains \(a\cdot 1=a\).
- `rightConvolution_actualAdelicEnvelopingAction_of_conjugation`: if \(\mathrm{Ad}(k)Y=Y\) for all \(k\in G(F_\infty)\), then by covariance \((Y\,R(g)f)(x)=(Yf)(xg)\). The previous item becomes the Harish-Chandra equation of \(Yf\).

## Compactness of the standard unipotent quotients

`Langlands.Global.AdelicSubgroupPoints.compactSpace_rationalQuotient_standardUnipotent`: for connected reductive \(G\), a maximal split torus with generic cocharacter and \(J\subseteq\Delta_0\), the quotient \(U_J(F)\backslash U_J(\mathbb A)\) is compact. The standard unipotent group scheme is a closed subgroup represented by the dynamic unipotent subgroup of a cocharacter (`standardCocharacter`). It is therefore smooth and connected (`dynamicSmooth`, `dynamicConnected`) and unipotent (`RepresentationGrowth.isUnipotent_standardUnipotentScheme`). The Library's `compactSpace_rationalQuotient_range_unipotent` then applies.

## Relation to Bernstein–Lapid

BL's \(V\) has one Harish-Chandra equation \(\delta(h)\phi=\phi\) and the constant-term equations of Lemma 8.1. Ξ_main has several Harish-Chandra equations, constant-term equations along all \(U_\alpha\), and central difference equations. BL call \(\mathfrak z\)-invariance clear. The proof here makes its two ingredients explicit: (a) derivatives commute with left-translation difference equations and with constant terms over compact quotients; (b) central elements commute with right convolution, which needs \(\mathrm{Ad}(G(F_\infty))\)-invariance of the center (the premise). The route through \(\Psi_a\) and induction over the enveloping algebra is internal. It avoids integration by parts against the test functions.

## Dependencies

Besides the published Library, the module imports two unpublished pairs, each a separate candidate. `AdelicLocalFinitenessCenterStabilityStatement` is byte-identical to candidate `f0ea9a64-b6f0-489f-bd2c-6418bbaddf8e`, and `GroupSchemeEnvelopingCenterConjugationStatement` to candidate `5d74a211-ef74-4f5b-bcee-afa5d6a3fd7e`. The entry declaration for staging is the definition `envelopingTranslate`. The main result is the theorem `localFinitenessCenterStability_of`.
