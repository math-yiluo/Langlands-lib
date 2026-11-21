# Stability of the solutions of Ξ_main under the center of the enveloping algebra

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), proof of Lemma 8.1 (§8.1, pp. 221–222), with the system Ξ_main of §7.2 (p. 211). In the proof of the "if" direction of Lemma 8.1, BL consider the space \(V\) of functions of uniform moderate growth satisfying the Harish-Chandra equation \(\delta(h)\phi=\phi\) and the difference equations for the constant terms. They write: "Hence \(V\) is finite-dimensional by Theorem 7.2. Clearly, \(V\) is \(\mathfrak z\)-invariant. Therefore, any \(\phi\in V\) is \(\mathfrak z\)-finite". This statement is the sentence "Clearly, \(V\) is \(\mathfrak z\)-invariant", formulated for the solution sets of Ξ_main used in the Library.

## The statement `Langlands.Global.LocalFinitenessCenterStabilityStatement`

The binders are those of the published `UniformGrowthLocalFinitenessStatement` (Theorem 7.2): a number field \(F\), a connected reductive \(G\), a maximal split torus \(i_T:T\to G\) with a generic cocharacter \(\nu\), group data \(u,t,z\) of Ξ_main (`IsLocalFinitenessGroupData`), a closed matrix embedding `rho` of positive size, the smooth structure `hsmooth` with its commutator datum `hcalc`, an open set \(W\subseteq\mathbb C^n\) and admissible analytic data \(X\) of Ξ_main on \(W\) (`LocalFinitenessData.IsAdmissible`), and a compact open subgroup \(L\le G(\mathbb A_f)\).

The conclusion is the following. Let \(R\) be real and \(s\in W\). Let \(v\in\mathfrak F^R_L\) be a solution of Ξ_main\((s)\), that is \(v\in\) `X.solutions … R L s`. Let \(Y\) be an element of the center `AdelicEnvelopingCenter F G hsmooth` of the complex enveloping algebra. Then some solution \(w\in\mathfrak F^R_L\) of Ξ_main\((s)\) has underlying element \(Y\cdot v\) of the carrier `FinitePlotSmoothRationalFunctions`, where the action is the Library's `adelicCenterAction`. In particular \(Y\cdot v\) lies in \(\mathfrak F^R_L\) itself.

## Why it holds, and what a proof needs

The solution set is defined by three kinds of equations.

1. The Harish-Chandra equations \(\sum_k b_{i,k}(s)\,\delta(h_{i,k})f=c_i(s)f\). For a test function \(h\), the right derivative of \(\delta(h)f\) along \(Y\) is \(\int h(g)\,(\mathrm{Ad}(g^{-1})Y\,f)(xg)\,dg\). Since \(G\) is connected, \(\mathrm{Ad}(G(F_\infty))\) fixes the center of the enveloping algebra, so \(Y\delta(h)f=\delta(h)Yf\).
2. The constant-term equations \(D_\alpha(s)(a_\alpha)\,C_{U_\alpha}f=0\). Constant terms are integrals of left translates, and left translations commute with right derivatives, so \(C_{U_\alpha}(Yf)=Y\,C_{U_\alpha}f\). The same holds for the difference operators of left translation by \(a_\alpha\).
3. The central equations \(D_j(s)(z_j)f=0\). These are again left translations.

Finally \(Y\) preserves \(\mathfrak F^R_L\). The growth bounds of \(\mathfrak F^R_L\) are imposed on all derivatives with one exponent \(R\). Invariance under \(L\) is right translation by finite adelic points, which commutes with the archimedean derivatives.

A proof must justify differentiation under the integral sign in the first two items. In the first item it uses the compact support of the kernels, and in the second the compactness of \(U_\alpha(F)\backslash U_\alpha(\mathbb A)\).

## Use

The statement is a premise of `localFinitenessSolutionAutomorphy_of` (module `AdelicLocalFinitenessSolutionAutomorphy`). There, together with Theorem 7.2, it yields \(\mathfrak z\)-finiteness of every solution of Ξ_main. Its provenance is derived: BL assert the \(\mathfrak z\)-invariance without proof ("Clearly"). The formulation for the Library's solution sets, the carrier action `adelicCenterAction` and the quantifiers over \(L\), \(R\), \(s\) is internal to that reduction.
