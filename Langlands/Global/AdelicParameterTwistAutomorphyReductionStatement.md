# Automorphy of twists from center finiteness of twists

Module `Langlands.Global.AdelicParameterTwistAutomorphyReductionStatement`. It contains one
statement, `Langlands.Global.ParameterTwistAutomorphyReductionStatement`, and no proof. The proof
is `Langlands.Global.parameterTwistAutomorphyReduction` in the module
`Langlands.Global.AdelicParameterTwistAutomorphyReduction`.

## Statement

`ParameterTwistAutomorphyReductionStatement.{u}` is the implication

`ParameterTwistCenterFiniteStatement.{u} → ParameterTwistAutomorphyStatement.{u}`.

- `ParameterTwistAutomorphyStatement` (module `AdelicParameterTwistAutomorphyStatement`):
  for a standard parabolic family `fam`, a standard index \(I\), a maximal compact subgroup
  \(K\) of \(G(\mathbb A)\) with \(P_I(\mathbb A)K=G(\mathbb A)\) and the further good-position
  hypotheses of that statement, and a closed matrix embedding `rho`, every function \(\varphi\)
  automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) (`fam.IsAutomorphicOn`) has
  automorphic twists \(\varphi_\lambda=\varphi\cdot m_{P_I}^\lambda\) for all
  \(\lambda\in X^*(P_I)\otimes\mathbb C\).
- `ParameterTwistCenterFiniteStatement` (module `AdelicParameterTwistCenterFiniteStatement`):
  in the same setting, for a maximal compact subgroup \(K\) of \(G(\mathbb A)\) with
  \(P_I(\mathbb A)K=G(\mathbb A)\), the twist of a smooth, left \(U_I(\mathbb A)\)-invariant,
  \(\mathfrak z\)-finite function is \(\mathfrak z\)-finite. Of the hypotheses on \(K\) in
  `ParameterTwistAutomorphyStatement` it drops Iwasawa coverage for the minimal standard
  parabolic and the maximal compactness of the intersections of \(K\) with all standard Levi
  subgroups.

The premise is not proved in this module.

## Source and provenance

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.2, p. 191: "We have
\(\varphi_\lambda\in\mathcal A_P\)", with \(\mathcal A_P\) the automorphic forms on \(X_P\) of
Mœglin–Waldspurger I.2.17 (literature id `moeglin-waldspurger-1995-spectral-decomposition`,
printed pp. 37–38).

Provenance: derived. The automorphy predicate `IsAutomorphicFunctionOn` (module
`GroupSchemeInvariantForms`) has five conditions: left invariance, smoothness, finiteness under
the archimedean part of \(K\), \(\mathfrak z\)-finiteness and moderate growth. Bernstein–Lapid
give no argument for their assertion. The implication isolates \(\mathfrak z\)-finiteness, whose
proof in Mœglin–Waldspurger I.2.17 needs the Harish-Chandra homomorphism; the other four
conditions follow from properties of the Iwasawa height that are proved in the Library.
