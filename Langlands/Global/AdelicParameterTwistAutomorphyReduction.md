# Automorphy of twists from center finiteness of twists: proof

Module `Langlands.Global.AdelicParameterTwistAutomorphyReduction` proves
`Langlands.Global.ParameterTwistAutomorphyReductionStatement.{u}` (module
`Langlands.Global.AdelicParameterTwistAutomorphyReductionStatement`) as the theorem
`Langlands.Global.parameterTwistAutomorphyReduction`, which is
`Langlands.Global.parameterTwistAutomorphy_of_centerFinite`:

`ParameterTwistCenterFiniteStatement.{u} → ParameterTwistAutomorphyStatement.{u}`.

The premise is not proved here. Lean reports the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Notation: \(\varphi_\lambda=\) `hK.parameterTwist φ λ`, that is
\(\varphi_\lambda(g)=\varphi(g)\,m_P(g)^\lambda\) with \(m_P(g)^\lambda=\) `hK.heightPower λ g`
\(=\exp\langle\lambda,H_P(g)\rangle\) and the Iwasawa height \(H_P\) of a compact \(K\) with
\(P(\mathbb A)K=G(\mathbb A)\) (`IsIwasawaCompact.height`).

## Auxiliary results

All are in the namespace `Langlands.Global.AdelicGroupPoints`, for a closed subgroup
`p : P ⟶ G` of affine group schemes over a number field and `hK : IsIwasawaCompact p K`.

- `IsIwasawaCompact.heightPower_mul_right`: \(m_P(gk)^\lambda=m_P(g)^\lambda\) for \(k\in K\),
  from `IsIwasawaCompact.height_mul_right`.
- `IsIwasawaCompact.isLeftInvariantUnder_parameterTwist`: for `iU : U ⟶ P` with `U` unipotent
  and `l : M ⟶ P`, if \(\varphi\) is left invariant under `parabolicQuotientSubgroup F p iU l`
  (the join of the images of \(U(\mathbb A)\) and \(M(F)\)), so is \(\varphi_\lambda\). The
  factor \(m_P^\lambda\) is left invariant under the join by `isLeftInvariantUnder_sup`: under
  \(U(\mathbb A)\) by `IsIwasawaCompact.heightPower_unipotent_mul`, and under \(M(F)\) by
  `IsIwasawaCompact.heightPower_rational_mul`, after writing the image of a rational point of
  \(M\) as the image of a rational point of \(P\) (`map_comp_apply_of_hom`,
  `map_rational_eq_rational`).
- `IsIwasawaCompact.isAdelicSmoothFunction_parameterTwist`: for \(K\) maximal compact and a
  smooth structure `hsmooth`, the twist of a function satisfying `IsAdelicSmoothFunction`
  satisfies it.
  - Continuity: `IsIwasawaCompact.continuous_parameterTwist`.
  - Plot-smooth infinite slices: by `isPlotSmooth_iff_contMDiff` the slices of \(\varphi\) are
    smooth maps; the height pairings are smooth on the slices
    (`IsIwasawaCompact.hasSmoothHeightPairings_of_maximalCompact`), so the slices of the twist
    are smooth (`IsIwasawaCompact.contMDiff_parameterTwist_slice`).
  - Finite level: if the open subgroup \(L\) of \(G(\mathbb A_f)\) fixes \(\varphi\), the open
    subgroup \(L\cap\mathrm{pr}_f(K)\) (`IsMaximalCompactSubgroup.isOpen_finite`) lies in \(K\)
    (`IsMaximalCompactSubgroup.map_finite_le_comap_ofFinite`), so it also fixes
    \(m_P^\lambda\) and hence \(\varphi_\lambda\).
- `IsIwasawaCompact.isInfiniteSubgroupFiniteFunction_parameterTwist`: for
  \(K_\infty=\) `K.comap (ofInfinite F G)`, the right \(K_\infty\)-translates of
  \(\varphi_\lambda\) are the images of those of \(\varphi\) under the linear map
  \(f\mapsto f\cdot m_P^\lambda\) (by `heightPower_mul_right`), so their span is the image of a
  finite-dimensional space (`Submodule.span_image`).
- `IsIwasawaCompact.hasModerateGrowthFunction_parameterTwist`: for a closed matrix embedding
  `rho`, if \(\|\varphi(g)\|\le C\|g\|^r\) for the adelic source norm \(\|g\|\) of `rho`, then
  \(\|\varphi_\lambda(g)\|\le C A s^e\|g\|^{r+e}\), where
  \(\|m_P(g)^\lambda\|\le A\,\mathrm{ht}(g)^e\)
  (`IsIwasawaCompact.exists_norm_heightPower_le_adelicHeight`) and \(\mathrm{ht}(g)=s\|g\|\)
  for the constant \(s=N^{\sum_v m_v}\) (`adelicHeight_eq_scalar_mul_sourceNorm`). If the matrix
  size \(N\) is \(0\), the adelic points form a trivial group
  (`subsingleton_adelicGroupPoints_of_closed_zeroMatrix`) and a constant bound works.

## The main proof (`parameterTwistAutomorphy_of_centerFinite`)

Fix the data of `ParameterTwistAutomorphyStatement` and an automorphic \(\varphi\). The predicate
`fam.IsAutomorphicOn` is `IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F (fam.p I)
(fam.iU I) (fam.l I)`, the archimedean part of \(K\) and `rho`, with the canonical commutator
datum. Its five conditions for \(\varphi_\lambda\) are:

1. left invariance, by `isLeftInvariantUnder_parameterTwist`, with `U_I` unipotent since
   `fam.iU I` is a geometric unipotent radical (`fam.isUnipotentRadical I`);
2. smoothness, by `isAdelicSmoothFunction_parameterTwist` and the maximality of \(K\);
3. finiteness under the archimedean part of \(K\), by
   `isInfiniteSubgroupFiniteFunction_parameterTwist`;
4. \(\mathfrak z\)-finiteness, by the premise `ParameterTwistCenterFiniteStatement`, applied to
   the left invariance of \(\varphi\) under the image of \(U_I(\mathbb A)\) (contained in
   `parabolicQuotientSubgroup`), its smoothness and its \(\mathfrak z\)-finiteness;
5. moderate growth, by `hasModerateGrowthFunction_parameterTwist` and the closedness of `rho`.

The hypotheses of `ParameterTwistAutomorphyStatement` on Iwasawa coverage for the minimal
standard parabolic and on the intersections of \(K\) with the standard Levis are not used.

## Provenance

The conclusion is Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §2.2, p. 191 ("We have \(\varphi_\lambda\in\mathcal A_P\)",
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), with the conditions
of Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.2.17, printed
pp. 37–38 (registered as `moeglin-waldspurger-1995-spectral-decomposition`). The sources give
no argument for the four conditions proved here; the arguments above are internal to the
Library and use its Iwasawa height.
