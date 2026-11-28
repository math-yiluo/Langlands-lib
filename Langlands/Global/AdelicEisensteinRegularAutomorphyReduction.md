# Automorphy of convergent Eisenstein series from automorphy of twists: proof

Module `Langlands.Global.AdelicEisensteinRegularAutomorphyReduction` proves
`Langlands.Global.EisensteinRegularAutomorphyReductionStatement.{u}` (module
`Langlands.Global.AdelicEisensteinRegularAutomorphyReductionStatement`) as the theorem
`Langlands.Global.eisensteinRegularAutomorphyReduction`:

`ParameterTwistAutomorphyStatement.{u} → EisensteinRegularAutomorphyStatement.{u}`.

The premise is not proved here. Lean reports the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Notation: for a closed subgroup `p : P ⟶ G` and `hK : IsIwasawaCompact p K`,
\(\varphi_\lambda=\) `hK.parameterTwist φ λ`, \(\varphi_\lambda(g)=\varphi(g)\,m_P(g)^\lambda\)
with \(m_P(g)^\lambda=\) `hK.heightPower λ g` \(=\exp\langle\lambda,H_P(g)\rangle\) and the
Iwasawa height \(H_P\) of \(K\). The Eisenstein series \(E(\varphi,\lambda)=\)
`hK.eisensteinSeries φ λ` is the unconditional sum over \(c\in P(F)\backslash G(F)\) of the terms
`hK.eisensteinTerm φ λ g c` \(=\varphi_\lambda(\gamma_c g)\), with \(\gamma_c\) the chosen
representative of \(c\). \(K_\infty\) is `K.comap (ofInfinite F G)`. The infinite slice of a
function \(f\) at a finite adelic point \(b\) is \(x\mapsto f(x,b)\) (`functionInfiniteSlice`), and
the enveloping algebra acts on plot-smooth slices by `plotSmoothEnvelopingAction`.

## Termwise differentiation (`exists_plotSmooth_tsum_envelopingAction`)

Let \(f_i\) be plot-smooth functions on the archimedean points \(G(F_\infty)\), \(m\ge0\) a summable
family and \(w\) a continuous function such that for every enveloping element \(a\) there is
\(C_a\ge0\) with \(|(a f_i)(x)|\le C_a m_i w(x)\) for all \(i\) and \(x\). Then there is a
plot-smooth \(g\) with \((a g)(x)=\sum_i (a f_i)(x)\) for every \(a\) and \(x\); for \(a=1\) this
says that \(g\) is the pointwise sum.

Proof. On each compact set the bound gives uniform convergence of the partial sums of every
derivative series (`tendstoUniformlyOn_tsum`). The invariant-derivative limit theorem
`contMDiff_of_tendstoLocallyUniformly_invariantDerivatives` (module `SmoothGroupUniformLimit`),
applied to the partial sums of \(a f_i\) for all \(a\) at once, shows that every sum
\(s_a=\sum_i a f_i\) is smooth and that the derivative of \(s_a\) along a real Lie algebra
element \(X\) is \(s_{Xa}\). The map \(a\mapsto s_a\) is \(\mathbb C\)-linear, and induction over
the tensor algebra presenting the enveloping algebra extends \(X s_a=s_{Xa}\) to
\(b\,s_a=s_{ba}\) for all \(b\). Then \(g=s_1\) satisfies \(a g=s_a\). The argument is the one
of the private lemma in the proof of `eisensteinCommonGrowth` (module
`AdelicEisensteinCommonGrowthProof`), with the identification of the derivatives of the sum kept
in the conclusion.

## Right translation by `K`

- `IsIwasawaCompact.rightTranslate_mem_compactMajorantSections`: if the terms of \(\varphi\) have a
  summable majorant on every compact set (`hK.compactMajorantSections λ`, module
  `AdelicEisensteinLinearConvergence`), so do those of \(g\mapsto\varphi(gk)\) for \(k\in K\).
  The term of the translate at \(x\) is the term of \(\varphi\) at \(xk\), by right
  \(K\)-invariance of the height (`IsIwasawaCompact.height_mul_right`); use the majorant on the
  compact set \(Ck\).
- `IsIwasawaCompact.eisensteinSeries_isInfiniteSubgroupFiniteFunction`: let \(K'\) be a subgroup
  of \(G(F_\infty)\) whose image lies in \(K\). If \(\varphi\) is \(K'\)-finite and its terms have
  compact summable majorants at \(\lambda\), then \(E(\varphi,\lambda)\) is \(K'\)-finite. The span
  \(V\) of the translates \(\varphi(\cdot\,k)\), \(k\in K'\), is finite-dimensional and lies in
  `hK.compactMajorantSections λ` by the previous item, where the series is linear
  (`eisensteinSeriesLinear`). For \(k\in K\) the translate of \(E(\varphi,\lambda)\) by \(k\) is
  the series of \(\varphi(\cdot\,k)\) (`eisensteinSeries_parameterRightAction` and
  `parameterRightAction_compact`, module `AdelicEisensteinRightTranslation`). So the translates
  of \(E(\varphi,\lambda)\) lie in the image of \(V\), a finite-dimensional space.

## Regular series (`exists_regular_eisensteinSeries_slices`)

The setting is that of `EisensteinCommonGrowthStatement`: a parabolic `p : P ⟶ G` with root
presentation `r`, split-torus witnesses `hA`, `hT`, connected reductive \(G\), unipotent radical
`iU`, a maximal compact \(K\) with `hK`, a closed matrix embedding `rho` of positive size \(N\),
`hsmooth`, `hcalc`, and \(\varphi\) automorphic on `parabolicQuotientSubgroup F p iU l` for
\(K_\infty\). The theorem gives \(R_0\) such that for every \(R_0\)-regular \(\lambda\):
\(E(\varphi,\lambda)\) is smooth (`IsAdelicSmoothFunction`) and of moderate growth for `rho`;
\(\varphi\in\) `hK.compactMajorantSections λ`; and every enveloping element annihilating all
infinite slices of \(\varphi_\lambda\) annihilates all infinite slices of \(E(\varphi,\lambda)\).

Proof. The construction of the majorant follows the proof of `eisensteinCommonGrowth`. The
elliptic estimate `exists_uniformGrowth_functionInfiniteSlices` gives a common exponent \(e_0\)
for the derivatives of \(\varphi\) in the adelic matrix height \(\mathrm{ht}\) of `rho`.
Representatives \(\gamma_c\) of the cosets are chosen with \(\mathrm{ht}(\gamma_c)\le B h(c)^{d_0}\)
for the projective height \(h(c)\) (`exists_polynomial_rationalCoset_representatives`), and
\(t\ge0\) with \(\sum_c h(c)^{-t}<\infty\) (`summable_projectivization_mulHeight_rpow`). The
threshold \(R_0\) is the one of `IsIwasawaCompact.exists_norm_heightPower_rational_le_projectiveHeight`
for the decay order \(d_0e_0+t\); it does not depend on \(\lambda\). Fix an \(R_0\)-regular
\(\lambda\), and use the one-dimensional coordinate \(s\mapsto s_0\lambda\) at \(s=1\): projective
decay gives \(|m_P(\gamma_c)^\lambda|\le B_2 h(c)^{-d_0e_0-t}\), and
`IsIwasawaCompact.exists_uniform_heightPower_mul_le` gives
\(|m_P(xg)^\lambda|\le B_1\mathrm{ht}(g)^{d_1}|m_P(x)^\lambda|\). With the derivative bound for the
twist (`IsIwasawaCompact.exists_parameterTwist_derivative_bound`) and submultiplicativity of
\(\mathrm{ht}\), every derivative \(D\) of the term on the slice at \(b\), which is the left
translate by \(\gamma_{c,\infty}\) of the slice of \(\varphi_\lambda\) at \(\gamma_{c,f}b\)
(`plotSmoothEnvelopingAction_leftTranslate`), is bounded by
\(C_D\,h(c)^{-t}\,\mathrm{ht}(x,b)^{R_1}\) with \(R_1=e_0+d_1\).

Termwise differentiation on each slice gives plot-smooth slices whose values are those of
\(E(\varphi,\lambda)\) and whose derivatives are the sums of the derivatives of the terms. Then:

- smoothness: continuity from the slices and right invariance under the open subgroup
  \(L_0\cap\mathrm{pr}_f(K)\) of \(G(\mathbb A_f)\), where \(L_0\) fixes \(\varphi\)
  (`continuous_evaluatePlotSmoothSlices`, `IsMaximalCompactSubgroup.isOpen_finite`);
- moderate growth: the bound for \(D=1\) gives
  \(|E(\varphi,\lambda)(g)|\le C_1(\sum_c h(c)^{-t})\,\mathrm{ht}(g)^{R_1}\), and
  \(\mathrm{ht}=s\,\|\cdot\|\) for the source norm and a constant \(s\)
  (`adelicHeight_eq_scalar_mul_sourceNorm`);
- compact majorants: the same bound with the maximum of \(\mathrm{ht}^{R_1}\) on a compact set;
- annihilators: if \(D\) kills every slice of \(\varphi_\lambda\), it kills every term, since it
  commutes with left translation, hence the sum of the derivatives of the terms, which is the
  derivative of the slice of \(E(\varphi,\lambda)\).

## Automorphy (`exists_regular_eisensteinSeries_isAutomorphicFunctionOn`)

In the same setting there is \(R_0\) such that for every \(R_0\)-regular \(\lambda\) at which
\(\varphi_\lambda\) is \(\mathfrak z\)-finite (`IsCenterFiniteFunction`), \(E(\varphi,\lambda)\) is
automorphic on \(G(F)\backslash G(\mathbb A)\) for \(K_\infty\) and `rho`. The five conditions of
`IsAutomorphicFunctionOn`: left \(G(F)\)-invariance is `eisensteinSeries_leftRationalInvariant`
(module `AdelicWavePacketRationalInvariance`); smoothness and moderate growth come from the
previous theorem; \(K_\infty\)-finiteness from `eisensteinSeries_isInfiniteSubgroupFiniteFunction`
with the finiteness of \(\varphi\) and its compact majorants; and an ideal of finite codimension in
the center that annihilates the slices of \(\varphi_\lambda\) annihilates those of
\(E(\varphi,\lambda)\), since the center acts through the enveloping algebra
(`plotSmoothCenterAction`).

## The reduction (`eisensteinRegularAutomorphyReduction`)

Assume `ParameterTwistAutomorphyStatement` and take the data of
`EisensteinRegularAutomorphyStatement`. The premise makes every twist \(\varphi_\lambda\)
automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\).

- If the matrix size is \(N=0\), `rho` is a closed immersion into the trivial group, so
  \(G(\mathbb A)\) has at most one element (`MatrixRepresentation.pointMatrix_injective`). Then
  \(G(F)\) and \(P(F)\backslash G(F)\) have one element, the series is the single term, and
  \(E(\varphi,\lambda)=\varphi_\lambda\) for every \(\lambda\). The premise gives smoothness,
  \(K_\infty\)-finiteness, \(\mathfrak z\)-finiteness and moderate growth of \(\varphi_\lambda\);
  left invariance holds in a group with one element. Any threshold works; the proof takes \(0\).
- If \(N>0\), apply `exists_regular_eisensteinSeries_isAutomorphicFunctionOn` to the standard
  presentation `r` of \(P_I\), with the connected reductivity and the unipotent radical from
  `fam` and the canonical commutator datum; its threshold \(R_0\) does not depend on
  \(\lambda\), and the premise supplies the \(\mathfrak z\)-finiteness of \(\varphi_\lambda\).

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234 (literature id
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §2.2, p. 191, and Theorem 2.3 (1),
  p. 191.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995)
  (literature id `moeglin-waldspurger-1995-spectral-decomposition`), chapter file
  `06.1_pp_78_100_Definitions.pdf`, II.1.5, printed pp. 85–87: termwise estimates for convergent
  Eisenstein series. The majorant used here is the Library's projective-height majorant, which
  covers arbitrary automorphic inducing data.
