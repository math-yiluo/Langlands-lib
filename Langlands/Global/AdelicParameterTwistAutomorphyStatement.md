# Twists of automorphic forms on a parabolic quotient

Module `Langlands.Global.AdelicParameterTwistAutomorphyStatement`. It contains one statement, `Langlands.Global.ParameterTwistAutomorphyStatement`, and no proof.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.2, p. 191, just before (2.1): "Denote by \(\mathcal A_P\) the space of automorphic forms on \(X_P\) [28, I.2.17]. For any \(\varphi\in\mathcal A_P\) and \(\lambda\in\mathfrak X_P\) set \(\varphi_\lambda(g)=\varphi(g)m_P(g)^\lambda\). We have \(\varphi_\lambda\in\mathcal A_P\)." Reference [28] is Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995).

Provenance: source. The statement is this assertion for the standard parabolics of a standard parabolic family, with \(K\) in good position as in the setting of Bernstein–Lapid §2.1.

## Statement

The binders are:

- a number field \(F\) and an affine group scheme \(G\) of finite type over \(F\);
- a standard parabolic family `fam` (module `AdelicLeadingCuspidalComponents`), which includes the connected reductivity of \(G\), and a standard index \(I\), with the parabolic \(P_I\) embedded by the closed immersion `fam.p I`;
- a subgroup \(K\) of \(G(\mathbb A)\) with `hK : IsIwasawaCompact (fam.p I) K`, that is \(P_I(\mathbb A)K=G(\mathbb A)\);
- a closed matrix embedding `rho` (`IsClosedSubgroup rho`) and the smooth structure `hsmooth`.

The hypotheses on \(K\) are:

- it is a maximal compact subgroup of \(G(\mathbb A)\) (`IsMaximalCompactSubgroup`);
- it satisfies Iwasawa coverage for the minimal standard parabolic (index \(\emptyset\));
- it meets every standard Levi \(M_J(\mathbb A)\) in a maximal compact subgroup of \(M_J(\mathbb A)\), the comap along `fam.l J ≫ fam.p J`.

These are the good-position hypotheses used in the Library's statements on cuspidal projections, for example `CuspidalProjectionDecompositionStatement` (module `AdelicCuspidalProjectionDecompositionStatement`).

**Assertion.** Let \(\varphi\) be automorphic on \(X_{P_I}=U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) for the archimedean part \(K_\infty\) of \(K\) (the comap of \(K\) along `ofInfinite`) and for `rho`. This is `fam.IsAutomorphicOn hsmooth Kinf rho I φ`, which uses the canonical commutator datum. Then for every \(\lambda\in X^*(P_I)\otimes\mathbb C\) (`ComplexCharacterParameter F (fam.P I)`), the twist \(\varphi_\lambda\) is again automorphic on \(X_{P_I}\) in the same sense.

The twist is `hK.parameterTwist φ λ` (module `AdelicEisensteinSeries`), the function \(g\mapsto\varphi(g)\,m_{P_I}(g)^\lambda\) with \(m_{P_I}(g)^\lambda=\exp\langle\lambda,H_{P_I}(g)\rangle\) (`IsIwasawaCompact.heightPower`). Here \(H_{P_I}\) is the Iwasawa height of \(K\) (`IsIwasawaCompact.height`, module `AdelicIwasawaHeight`).

## Correspondence with the source

The Library's predicate `IsAutomorphicOn` is `IsAutomorphicFunctionOn` (module `GroupSchemeInvariantForms`, after Mœglin–Waldspurger I.2.17) for the subgroup `parabolicQuotientSubgroup`, which is \(U_I(\mathbb A)M_I(F)\). The predicate consists of left invariance, smoothness, \(K_\infty\)-finiteness, finiteness under the center of the enveloping algebra, and moderate growth for the norm of `rho`. So the statement is Bernstein–Lapid's \(\varphi_\lambda\in\mathcal A_P\) for \(P=P_I\). The space \(\mathcal X_P\) of the source is \(X^*(P)\otimes\mathbb C\) in the number field case.

The reasons for the source assertion, by component of the predicate:

- **Left invariance.** By `IsIwasawaCompact.height_unipotent_mul` and `IsIwasawaCompact.height_rational_mul` (module `AdelicIwasawaHeight`), the height is invariant under left translation by \(U_I(\mathbb A)\) and by \(M_I(F)\). The latter holds by the product formula.
- **Smoothness and \(K_\infty\)-finiteness.** \(H_{P_I}\) is right \(K\)-invariant (`IsIwasawaCompact.height_mul_right`). It is continuous, smooth in the archimedean variable and locally constant in the finite variable, so \(m_{P_I}^\lambda\) multiplies the right \(K_\infty\)-translates of \(\varphi\) by one fixed smooth function.
- **Moderate growth.** \(|m_{P_I}(g)^\lambda|\) is bounded by a power of the norm of \(g\).
- **Center finiteness.** A function on \(U_I(\mathbb A)\backslash G(\mathbb A)\) is finite under the center \(\mathfrak z(\mathfrak g)\) exactly when it is finite under \(\mathfrak z(\mathfrak m_I)\), through the Harish-Chandra homomorphism. Multiplication by the character \(m_{P_I}^\lambda\) of \(M_I(\mathbb A)\) changes the \(\mathfrak z(\mathfrak m_I)\)-action by an automorphism of \(\mathfrak z(\mathfrak m_I)\), the translation by \(\lambda\).

## Use

The statement provides automorphy of \(\varphi_\lambda\) on \(X_{P_I}\). This is needed to form the cuspidal projections of \(C_{I,J}\varphi_\lambda\) along standard \(J\le I\) with `CuspidalProjectionDecompositionStatement`. For instance, the conditions (6.21) of Bernstein–Lapid involve \(C^{\mathrm{cusp}}_{P,Q}\varphi_\lambda\).
