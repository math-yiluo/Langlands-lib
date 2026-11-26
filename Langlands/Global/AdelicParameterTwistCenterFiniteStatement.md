# Center finiteness of twists on a parabolic quotient

Module `Langlands.Global.AdelicParameterTwistCenterFiniteStatement`. It contains one statement,
`Langlands.Global.ParameterTwistCenterFiniteStatement`, and no proof.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234 (literature id
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.2, p. 191, just before (2.1):
  "For any \(\varphi\in\mathcal A_P\) and \(\lambda\in\mathfrak X_P\) set
  \(\varphi_\lambda(g)=\varphi(g)m_P(g)^\lambda\). We have \(\varphi_\lambda\in\mathcal A_P\)."
  Here \(\mathcal A_P\) is the space of automorphic forms on \(X_P\) of [28, I.2.17].
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
  (literature id `moeglin-waldspurger-1995-spectral-decomposition`), chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, I.2.17, printed pp. 37–38:
  the definition of automorphic forms on \(U(\mathbb A)M(k)\backslash G\) by the conditions
  (i) moderate growth, (ii) smoothness, (iii) \(K\)-finiteness, (iv) \(\mathfrak z\)-finiteness,
  and the proof of the reduction to \(M\), which uses the Harish-Chandra homomorphism
  \(i:\mathfrak z\to\mathfrak z_M\). The compatibility of \(i\) printed there omits a
  normalization; see the argument below.

Provenance: derived. Bernstein–Lapid assert \(\varphi_\lambda\in\mathcal A_P\). The statement here
is the part of that assertion which concerns condition (iv), \(\mathfrak z\)-finiteness, for the
standard parabolics of a standard parabolic family and a maximal compact subgroup \(K\) with
\(P(\mathbb A)K=G(\mathbb A)\). It is stated for every smooth function on \(U(\mathbb A)\backslash
G(\mathbb A)\) that is \(\mathfrak z\)-finite, without the conditions of \(K\)-finiteness, moderate
growth and left \(M(F)\)-invariance, because the argument below uses none of them. That argument
combines the corrected Harish-Chandra compatibility of Mœglin–Waldspurger I.2.17 with the finite
generation of \(\mathfrak z_M\) over \(i(\mathfrak z)\); neither source writes it out for twists.

## Statement

The binders are:

- a number field \(F\) and an affine group scheme \(G\) of finite type over \(F\);
- a standard parabolic family `fam` (module `AdelicLeadingCuspidalComponents`), which includes
  the connected reductivity of \(G\), and a standard index \(I\), with the parabolic \(P_I\)
  embedded by the closed immersion `fam.p I` and its unipotent radical \(U_I\) embedded by
  `fam.iU I`;
- a subgroup \(K\) of \(G(\mathbb A)\) with `hK : IsIwasawaCompact (fam.p I) K`, that is
  \(K\) compact and \(P_I(\mathbb A)K=G(\mathbb A)\), which is a maximal compact subgroup of
  \(G(\mathbb A)\) (`IsMaximalCompactSubgroup`);
- the smooth structure `hsmooth : SmoothOfRelativeDimension d G.X.hom`, which gives the Lie group
  structure of the infinite adelic points, and a commutator datum
  `hcalc : AdelicDifferentialCommutator F G hsmooth` (a proposition, so the choice does not
  matter).

**Assertion.** Let \(\varphi\) be a complex function on \(G(\mathbb A)\) such that

- \(\varphi(ug)=\varphi(g)\) for \(u\) in the image of \(U_I(\mathbb A)\)
  (`IsLeftInvariantUnder` for `parabolicUnipotentImage F (fam.p I) (fam.iU I)`);
- \(\varphi\) is smooth (`IsAdelicSmoothFunction`: continuous, with plot-smooth infinite
  slices and a finite level);
- \(\varphi\) is \(\mathfrak z\)-finite (`IsCenterFiniteFunction`: one ideal of finite
  codimension in the center \(\mathfrak z\) of the complex enveloping algebra of the Lie algebra
  of \(G(F_\infty)\) annihilates every infinite slice \(a\mapsto\varphi(a,b)\)).

Then for every \(\lambda\in X^*(P_I)\otimes\mathbb C\) (`ComplexCharacterParameter F (fam.P I)`)
the twist \(\varphi_\lambda=\) `hK.parameterTwist φ λ`, the function
\(g\mapsto\varphi(g)\,m_{P_I}(g)^\lambda\) with \(m_{P_I}(g)^\lambda=\exp\langle\lambda,
H_{P_I}(g)\rangle\) and the Iwasawa height \(H_{P_I}\) of \(K\) (`IsIwasawaCompact.height`), is
again \(\mathfrak z\)-finite in the same sense.

## Why the statement holds

This file does not prove the statement. It holds by the following argument, which is built on
Mœglin–Waldspurger I.2.17 with the normalization there corrected.

*Actions.* Let \(V\) be the space of smooth functions on \(G(\mathbb A)\) that are left invariant
under \(U_I(\mathbb A)\). The center \(\mathfrak z\) acts on \(V\) by right differentiation in the
infinite coordinate; so a function is \(\mathfrak z\)-finite in the sense of
`IsCenterFiniteFunction` exactly when one ideal of finite codimension of \(\mathfrak z\) kills it.
Let \(\mathfrak m\) be the Lie algebra of \(M_I(F_\infty)\), and let \(\mathfrak z_M\) be the
center of its complex enveloping algebra \(U(\mathfrak m)\). Then \(U(\mathfrak m)\) acts on
functions on \(G(\mathbb A)\) by left differentiation in the infinite coordinate,
\(L(X)f(g)=\frac{d}{dt}f(\exp(-tX)g)\big|_{t=0}\) for \(X\in\mathfrak m\). For
\(\psi\in V\) put \(\psi'=m_P^{-\rho_P}\psi\), where \(\rho_P\) is the half-sum of the roots of
\(M_I\) in the Lie algebra of \(U_I\).

*Correction of the printed compatibility.* Mœglin–Waldspurger (p. 37) state that a homomorphism
\(i:\mathfrak z\to\mathfrak z_M\) of Harish-Chandra satisfies \(z\cdot\psi=i(z)\cdot\psi'\) for
\(\psi\in V\) and \(z\in\mathfrak z\). This display omits the normalization on the left side: at
\(z=1\) it would give \(\psi=m_P^{-\rho_P}\psi\), which fails for \(\psi\equiv1\) when \(U_I\) is
nontrivial. The correct compatibility is
\[(z\cdot\psi)'=L(i(z))\,\psi'\qquad(\psi\in V,\ z\in\mathfrak z).\]
The Library states this normalized compatibility, for the normalized restrictions
\(m\mapsto m^{-\rho_Q}f(mg)\) of functions on \(G(F_\infty)\) to a Levi subgroup, as
`LeviRestrictionCenterTransferStatement` (module `AdelicLeviCenterTransferStatement`).
Moreover \(\mathfrak z_M\) is a finitely generated module over \(i(\mathfrak z)\)
(Mœglin–Waldspurger p. 37, citing Harish-Chandra).

*The argument.* Let \(\varphi\in V\) and let \(J\subseteq\mathfrak z\) be an ideal of finite
codimension with \(z\cdot\varphi=0\) for all \(z\in J\).

1. By the corrected compatibility, \(L(i(z))\varphi'=(z\cdot\varphi)'=0\) for \(z\in J\). Hence
   the ideal \(J_M=\mathfrak z_M\,i(J)\) of \(\mathfrak z_M\) generated by \(i(J)\) kills
   \(\varphi'\). This holds as an identity of functions on \(G(\mathbb A)\), so at every point of
   every finite slice. The quotient \(\mathfrak z_M/J_M\) is spanned, as a module over the finite
   dimensional algebra \(\mathfrak z/J\) acting through \(i\), by finitely many generators of
   \(\mathfrak z_M\) over \(i(\mathfrak z)\). So \(J_M\) has finite codimension.
2. For \(m\in M_I(\mathbb A)\) and \(g\in G(\mathbb A)\),
   \(m_P(mg)^\lambda=m_P(m)^\lambda m_P(g)^\lambda\). Let \(d\lambda\) be the differential of the
   character \(m\mapsto m_P(m)^\lambda\) of \(M_I(F_\infty)\). It is a linear form on
   \(\mathfrak m\) that vanishes on \([\mathfrak m,\mathfrak m]\) and is invariant under the
   adjoint action. Let \(\tau_\lambda\) be the automorphism of \(U(\mathfrak m)\) with
   \(\tau_\lambda(X)=X+d\lambda(X)\) for \(X\in\mathfrak m\). It maps \(\mathfrak z_M\) onto
   itself, and the product rule gives \(L(\tau_\lambda(y))(m_P^\lambda f)=m_P^\lambda\,L(y)f\) for
   \(y\in U(\mathfrak m)\). Since \((\varphi_\lambda)'=m_P^\lambda\varphi'\), the ideal
   \(\tau_\lambda(J_M)\) of \(\mathfrak z_M\), again of finite codimension, kills
   \((\varphi_\lambda)'\).
3. Put \(J_\lambda=i^{-1}(\tau_\lambda(J_M))\). It is an ideal of \(\mathfrak z\) of finite
   codimension, because \(\mathfrak z/J_\lambda\) embeds into
   \(\mathfrak z_M/\tau_\lambda(J_M)\). The twist \(\varphi_\lambda\) lies in \(V\): it is smooth
   and left invariant under \(U_I(\mathbb A)\) by the properties of the Iwasawa height of a
   maximal compact \(K\) with \(P_I(\mathbb A)K=G(\mathbb A)\)
   (`IsIwasawaCompact.isAdelicSmoothFunction_parameterTwist` in the module
   `AdelicParameterTwistAutomorphyReduction`, and `IsIwasawaCompact.heightPower_unipotent_mul`
   in the module `EisensteinConstantTerm.Height`). For \(z\in J_\lambda\) the corrected
   compatibility gives \((z\cdot\varphi_\lambda)'=L(i(z))(\varphi_\lambda)'=0\). Since
   \(m_P^{-\rho_P}\) does not vanish, \(z\cdot\varphi_\lambda=0\).

So the one ideal \(J_\lambda\) of finite codimension kills every infinite slice of
\(\varphi_\lambda\).

## Use

`ParameterTwistAutomorphyReductionStatement` (module
`AdelicParameterTwistAutomorphyReductionStatement`) records that this statement implies
`ParameterTwistAutomorphyStatement`, the full assertion \(\varphi_\lambda\in\mathcal A_P\) of
Bernstein–Lapid §2.2. The proof of that implication is
`Langlands.Global.parameterTwistAutomorphyReduction` (module
`AdelicParameterTwistAutomorphyReduction`).
