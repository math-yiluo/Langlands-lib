# Solutions of Ξ_main are automorphic forms, as a reduction

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), proof of Lemma 8.1 (§8.1, pp. 221–222), with the system Ξ_main and Theorem 7.2 of §7.2 (p. 211). In that proof the space \(V\) of solutions is finite-dimensional by Theorem 7.2 and \(\mathfrak z\)-invariant, so its elements are \(\mathfrak z\)-finite. They are \(K\)-finite because the kernel \(h\) is bi-\(K\)-finite. Hence they are automorphic forms.

This module proves the statement `LocalFinitenessSolutionAutomorphyStatement` (module `AdelicLocalFinitenessSolutionAutomorphyStatement`) **conditionally**, from two premises:

- `h72 : UniformGrowthLocalFinitenessStatement` (published, module `AdelicLocalFinitenessStatement`), BL Theorem 7.2: near every parameter, and for every large enough growth exponent, the solutions of Ξ_main are of finite type;
- `hstab : LocalFinitenessCenterStabilityStatement` (module `AdelicLocalFinitenessCenterStabilityStatement`): the center of the enveloping algebra maps solutions of Ξ_main\((s)\) in \(\mathfrak F^R_L\) to solutions.

The \(K_\infty\)-finiteness of the solutions is proved here without further premises.

## Finiteness under \(K_\infty\)

- `infiniteSubgroupFiniteSubmodule F G K`: the functions \(\varphi\) on \(G(\mathbb A)\) whose right translates by \(K\le G(\mathbb A_\infty)\) span a finite-dimensional space (`IsInfiniteSubgroupFiniteFunction`) form a submodule. The span of the translates of \(\varphi+\psi\) lies in the sum of the two spans, and that of \(c\varphi\) in the span for \(\varphi\).
- `rightConvolution_mul_right`: \(\delta(h)f(x\kappa)=\delta(h(\kappa^{-1}\,\cdot))f(x)\). This is the substitution \(g\mapsto\kappa g\) in \(\int h(g)f(x\kappa g)\,dg\), allowed by left invariance of Haar measure (`integral_mul_left_eq_self`). No integrability is needed.
- `isInfiniteSubgroupFiniteFunction_rightConvolution`: let \(h\) be continuous with compact support, let \(g\mapsto h(g^{-1})\) be right \(K\)-finite, and let \(f\) be continuous. Then \(\delta(h)f\) is right \(K\)-finite. The left translates \(h(\kappa^{-1}\,\cdot)\) are the images of the right translates of \(g\mapsto h(g^{-1})\) under \(\psi\mapsto\psi(\cdot^{-1})\), so their span \(S\) is finite-dimensional. Every element of \(S\) is continuous with compact support, so \(\psi\mapsto\delta(\psi)f\) is linear on \(S\): the integrands are integrable. By the previous item every right translate of \(\delta(h)f\) lies in the finite-dimensional image of \(S\).
- `continuous_toFun_uniformGrowth`: the function of an element of \(\mathfrak F^R_L\) is continuous.
- `LocalFinitenessData.isInfiniteSubgroupFiniteFunction_of_mem_solutions`: let the data be admissible and the kernels \(h_{i,k}\) left \(K\)-finite. Then every solution of Ξ_main\((s)\) is right \(K\)-finite. Admissibility gives an \(i\) with \(c_i(s)\neq0\), and the Harish-Chandra equation gives \(f=c_i(s)^{-1}\sum_k b_{i,k}(s)\,\delta(h_{i,k})f\). Each term is \(K\)-finite by the previous items, since test functions are continuous with compact support.

## The main theorem `localFinitenessSolutionAutomorphy_of`

Fix the data, \(K_\infty\), \(L\), \(R\), \(s\) and a solution \(v\) with function \(f\). By the published comparison `isAutomorphicFunctionOn_evaluate_iff`, automorphy of \(f\) on \(G(F)\backslash G(\mathbb A)\) is equivalent to three conditions on the underlying element of `FinitePlotSmoothRationalFunctions`. Left invariance under \(G(F)\) and smoothness hold for every element of that carrier.

1. *\(K_\infty\)-finiteness*: the previous section, transported by `isInfiniteSubgroupFiniteFunction_evaluate_iff`.
2. *\(\mathfrak z\)-finiteness* (`IsAdelicCenterFinite`). Theorem 7.2 at \(s_0=s\) gives a neighbourhood \(U\ni s\) and \(R_0\). At the exponent \(R'=\max(R,R_0)\) it gives an injective \(\ell_s:\mathbb C^m\to\mathfrak F^{R'}_L\) whose range contains all solutions at \(s\). The inclusion \(\mathfrak F^R_L\to\mathfrak F^{R'}_L\) (`UniformGrowthFrechetSpace.inclusion`) preserves functions, so it maps solutions to solutions. Hence the underlying elements of all solutions in \(\mathfrak F^R_L\) lie in the finite-dimensional subspace \(E\), the image of \(\mathbb C^m\) in the carrier. By `hstab`, every \(Y\cdot v\) with \(Y\) central is the element of a solution, so the \(\mathfrak z\)-orbit of \(v\) lies in \(E\) (`adelicCenterOrbitSpan_eq_range`) and spans a finite-dimensional space.
3. *Moderate growth*: the order-zero case of the uniform growth bound of \(\mathfrak F^R_L\), with constant \(\max(C,1)\) and exponent \(R\).

## Relation to Bernstein–Lapid

BL's \(V\) uses one bi-\(K\)-finite kernel with \(\delta(h)\phi=\phi\). Ξ_main has several Harish-Chandra equations \(\sum_k b_{i,k}\delta(h_{i,k})f=c_if\) with some \(c_i(s)\neq0\). The \(K_\infty\)-finiteness argument above is the corresponding form of BL's remark "since \(h\) is bi-\(K\)-finite". It needs only left finiteness of the kernels. The \(\mathfrak z\)-invariance, which BL call clear, is the premise `hstab`. The finite-dimensionality is Theorem 7.2 at a possibly larger exponent, transported along the inclusion of the spaces \(\mathfrak F^R_L\).

## Dependencies

Besides the published Library, the module imports two unpublished pairs. `AdelicLocalFinitenessSolutionAutomorphyStatement` is byte-identical to candidate `7bdda931-f4f4-4581-a889-ccb2e30e3a75`. `AdelicLocalFinitenessCenterStabilityStatement` is a separate candidate.
