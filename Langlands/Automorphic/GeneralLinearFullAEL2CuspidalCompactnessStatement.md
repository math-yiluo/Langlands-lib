# Compactness of continuous cuspidal convolutions for adelic GL_n

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearFullAEL2CuspidalCompactnessStatement`
is a proposition definition. For a number field `F` and `n : ℕ`, set
`G = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
The group scheme supplies affineness and local finite type. The parameters
`hPD`, `hG`, `T`, `i`, `hi`, `I`, `e`, and `hc` retain the
parabolic–cocharacter theorem, connected reductivity, and the supplied
positive-central quotient data. These data consist of the central map
`i : T.toGrp ⟶ G`, injectivity and finite index of character restriction,
and the split-torus isomorphism `e` indexed by the finite type `I`.
Right invariance of Haar measure on `normOneSubgroup F G` is also retained.

The operator acts on `S = fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc`,
the closed subspace of `L²` for `positiveRationalQuotientHaarMeasure F G T i`
with almost-everywhere absolute convergence and vanishing of the mass-one
constant terms along every proper rational parabolic. For every
`f : C_c(AdelicGroupPoints F G, ℂ)` and its Haar integrability witness `hf`,
the proposition asserts

```lean
IsCompactOperator (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc
  Measure.haar f hf)
```

Here `Measure.haar` is the original left Haar measure on the full adelic
group. Continuity and compact support give the integrability witness.
At the same group data, the universal assertion in `f` and `hf` is exactly
the premise of `GroupSchemeFullAEL2CuspidalDecompositionStatement`
specialized to this `G`.

## Source and proof route

The statement is derived from Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), source `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Theorem 9.1.2 (printed p. 241, PDF p. 253) proves trace class for smooth
compact tests on $A_G \backslash G(\mathbb A_F)$. Lemma 9.3.1 and
Corollary 9.3.2 (p. 247) use compactness to deduce discreteness. Lemma 9.3.3
(pp. 247–248) gives the analytic route from a uniform evaluation bound.

For a smooth compactly supported adelic test $f$, integrate in the positive
factor $A$ of `normOneDecompositionMulEquiv`. With $N = G(\mathbb A_F)^1$,
the quotient weight is $f_A(y)=\int_A f(ay)\,da$ for $y\in N$, where
$ay$ uses the image of $A$ in the adelic group. Compact support projects
to the quotient, differentiation under the integral preserves smoothness at
infinity, and the positive factor acts trivially at the finite places. Choose
`normalizedPositiveHaarMeasure` for $da$.
`map_normalizedPositiveHaarMeasure_prod` gives the exact product formula
with the original full-group Haar. Since the right action factors through
`normOneProjection`, Fubini identifies the original integrated operator with
convolution by $f_A$ for norm-one Haar. The Library's
`positiveQuotientHomeomorph_rightTranslate` and
`measurePreserving_positiveQuotient` give the measured right-action model on
$G(F)\backslash N$, the same norm-one model as Getz–Hahn (2.22) (p. 69).

For the number-field estimate, §9.4 first uses restriction of scalars to
reduce to $\mathbb Q$. Use Proposition 9.4.7 (pp. 257–259) and the
Siegel-domain bounds in Definition 9.6.1 and Theorem 9.6.4 (pp. 263–264).
For $n\ge 2$, each reduced domain has a positive lower bound on its simple
root coordinates. Combining the rootwise estimate on those domains with
reduction-theory coverage (Theorem 2.7.2, p. 72) and rational left invariance
gives $\|R(f_A)\phi\|_\infty\le C_{f_A}\|\phi\|_2$ on the actual quotient.
The quotient for $n=0$ is trivial, and for $n=1$ it is a compact abelian
group by Theorem 2.6.3 (p. 69). In these cases the periodized test is a
continuous kernel on the quotient group, and Cauchy–Schwarz gives the
evaluation bound. The raw height in the printed Lemma 9.6.2 can grow along
rational translates of a single quotient point. [Chapter 9 source notes](../../notes/automorphic/getz-hahn-cuspidal-source-map.md)

On the finite-volume quotient, the bound yields Hilbert–Schmidt summability
for each smooth test operator. Indeed, apply Bessel's inequality to each
bounded evaluation functional on $S$ and integrate the bounds on finite
sums of squared basis images. Compactness then follows from
`Langlands.Analysis.OperatorIdeals.hilbertSchmidtCompact`.
The October 2026 errata, source
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
p. 3 (§9.5), places the image of the function-field smoothing operator
in the fixed-vector subspace. The estimate above uses the number-field
argument of §9.4.

Choose smooth compact tests $f_j$ converging to the full-group
continuous test $f$ in $L^1$ for the original Haar measure. The density
uses smooth compact approximation on the archimedean factors and locally
constant compact approximation on the finite adeles. By linearity in the
weight and `norm_fullAEL2CuspidalIntegratedAction_le`,
$\|R(f_j)-R(f)\|\le\int_{G(\mathbb A_F)}|f_j-f|$.
The compact operators on $S$ are closed in the operator norm, by
`isClosed_setOfPred_isCompactOperator`, so the original continuous-weight
operator is compact.
