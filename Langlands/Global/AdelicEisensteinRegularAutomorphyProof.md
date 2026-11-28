# Automorphy of convergent Eisenstein series for a standard family

In `Langlands.Global.AdelicEisensteinRegularAutomorphyProof`, the theorem
`Langlands.Global.eisensteinRegularAutomorphy` proves `EisensteinRegularAutomorphyStatement.{u}`
for an arbitrary universe `u`. For an automorphic inducing function \(\varphi\) on
\(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\), it gives a threshold \(R\) such that
the series \(E(\varphi,\lambda)\) is automorphic on \(G(F)\backslash G(\mathbb A)\)
for every \(R\)-regular \(\lambda\). The parabolic, the compact in good position and the
regularity condition are those of the statement.

## Proof

1. `parabolicLeviCenterRestriction` in `GroupSchemeLeviCenterRestrictionProof` supplies the
   finite map from the archimedean enveloping center of \(G\) to that of the Levi. The map
   intertwines the center actions under Levi restriction of left unipotent-invariant functions.
2. `parameterTwistCenterFiniteReduction` applies this map to the annihilator of the
   archimedean slices of \(\varphi\). It extends the ideal to the Levi center, where
   multiplication by the twisting character changes the action by a center endomorphism.
   Contracting the extended ideal along the composite yields a finite-codimensional ideal
   that annihilates every archimedean slice of \(\varphi_\lambda\).
   `parameterTwistAutomorphy_of_centerFinite` combines this with left quotient invariance,
   smoothness at finite level, \(K_\infty\)-finiteness and moderate growth of the twist.
3. `eisensteinRegularAutomorphyReduction` applies twist automorphy to the series. For a matrix
   embedding of positive size, the projective-height bound selects \(R\) before
   \(\lambda\) is fixed. Summable derivative bounds give smoothness at finite level and
   moderate growth and justify termwise differentiation. The terms are left translates of
   the twist, so the same center ideal annihilates their sum. Reindexing gives left rational
   invariance, and compact equivariance carries the finite-dimensional translate span of
   \(\varphi\) to a finite-dimensional space containing the translates of the series.
   For matrix size zero the adelic group is trivial and the series is the single twisted term.
   The proof takes \(R=0\) in this case.

## Sources

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §2.1, p. 190, sets the good-position convention. Section 2.2, p. 191, gives the twist
and series (2.1). This proof establishes the automorphy assertion of Theorem 2.3(1), p. 191, in
the region of absolute convergence. [Journal article](https://doi.org/10.1090/jams/1020)

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.17,
pp. 37–38, gives the finite Harish-Chandra transfer used for center finiteness.
The convergence argument in II.1.5, pp. 85–87, uses isotypic inducing data. The projective-height
estimate in the Lean proof applies to the automorphic inducing functions of Bernstein–Lapid.
