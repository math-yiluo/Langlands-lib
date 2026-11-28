# Automorphy of convergent Eisenstein series from automorphy of twists

Module `Langlands.Global.AdelicEisensteinRegularAutomorphyReductionStatement`. It contains one
statement, `Langlands.Global.EisensteinRegularAutomorphyReductionStatement`, and no proof. The
proof is `Langlands.Global.eisensteinRegularAutomorphyReduction` in the module
`Langlands.Global.AdelicEisensteinRegularAutomorphyReduction`.

## Statement

`EisensteinRegularAutomorphyReductionStatement.{u}` is the implication

`ParameterTwistAutomorphyStatement.{u} → EisensteinRegularAutomorphyStatement.{u}`.

Both sides are unchanged Library statements. They share the following data: a number field
\(F\), an affine group scheme \(G\) of finite type over \(F\), a standard parabolic family
`fam`, a standard index \(I\) with `fam.p I` a closed immersion, a subgroup \(K\) of
\(G(\mathbb A)\) with `hK : IsIwasawaCompact (fam.p I) K` (\(P_I(\mathbb A)K=G(\mathbb A)\)) that
is maximal compact, satisfies Iwasawa coverage for the minimal standard parabolic and meets every
standard Levi subgroup in a maximal compact subgroup, a closed matrix embedding `rho` and a smooth
structure `hsmooth`. Let \(K_\infty\) be the archimedean part of \(K\) (the comap along
`ofInfinite`).

- `ParameterTwistAutomorphyStatement` (module `AdelicParameterTwistAutomorphyStatement`): if
  \(\varphi\) is automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\)
  (`fam.IsAutomorphicOn hsmooth Kinf rho I φ`), then so is the twist
  \(\varphi_\lambda=\) `hK.parameterTwist φ λ`, \(\varphi_\lambda(g)=\varphi(g)\,m_{P_I}(g)^\lambda\),
  for every \(\lambda\in X^*(P_I)\otimes\mathbb C\). This premise is quantified over the shared
  data only, without the two instances below.
- `EisensteinRegularAutomorphyStatement` (module `AdelicEisensteinRegularAutomorphyStatement`):
  the consequent also takes a `Fintype` instance for the relative Weyl group of `fam.i` and a
  `Mono` instance for the underlying scheme morphism of `CommGroupScheme.groupHom (fam.f I)`.
  These instances enter the Weyl-induced form used in `r.IsRegularParameter`. For \(\varphi\) as
  above there is a real \(R\), chosen before the parameter, such that for every \(\lambda\) that
  is \(R\)-regular for the standard presentation `r` of \(P_I\), the Eisenstein series
  `hK.eisensteinSeries φ λ` is automorphic on \(G(F)\backslash G(\mathbb A)\)
  (`IsAutomorphicFunctionOn` for `rationalSubgroup F G`, \(K_\infty\), `rho` and the canonical
  commutator datum).

The premise is not proved in this module.

## Source and provenance

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234 (literature id
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §2.2, p. 191, "We have
  \(\varphi_\lambda\in\mathcal A_P\)" (the premise) and the series (2.1); Theorem 2.3 (1),
  p. 191, "Whenever regular, \(E(\varphi,\lambda)\in\mathcal A_G\)" (the conclusion, in the
  region of absolute convergence).
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*, Cambridge
  University Press, 1995 (literature id `moeglin-waldspurger-1995-spectral-decomposition`):
  I.2.17, printed pp. 37–38, automorphic forms on \(U(\mathbb A)M(k)\backslash G\); II.1.5,
  printed pp. 85–87, the termwise argument for the automorphy of a convergent Eisenstein series
  with isotypic inducing data.

Provenance: derived. `IsAutomorphicFunctionOn` (module `GroupSchemeInvariantForms`) has five
conditions: left invariance, smoothness, finiteness under \(K_\infty\), \(\mathfrak z\)-finiteness
and moderate growth. For the Eisenstein series, left \(G(F)\)-invariance, smoothness, moderate
growth and \(K_\infty\)-finiteness follow from the inducing function \(\varphi\) by termwise
estimates in the region of absolute convergence. The \(\mathfrak z\)-finiteness of
\(E(\varphi,\lambda)\) needs an ideal of finite codimension in the center of the enveloping
algebra that annihilates the twist \(\varphi_\lambda\); its terms are left translates of
\(\varphi_\lambda\), and invariant differential operators commute with left translation. The
implication isolates this input as the premise.
