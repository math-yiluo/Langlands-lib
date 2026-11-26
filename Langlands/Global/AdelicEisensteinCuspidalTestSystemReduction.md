# The cuspidal test system from its premises

Module `Langlands.Global.AdelicEisensteinCuspidalTestSystemReduction`.

The proposition `EisensteinCuspidalTestSystemReductionStatement` is the implication from six propositions to `EisensteinCuspidalTestSystemStatement` (module `AdelicEisensteinCuspidalTestSystemStatement`). The theorem `eisensteinCuspidalTestSystem_of` proves it. The module proves the implication only; it proves none of the six premises.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234: §2.1–2.2, pp. 189–191; §6.2 ((6.2), (6.3), (6.8)); §6.10 ((6.17)–(6.22), pp. 207–209); §8.1 (the difference operators, p. 222); §8.4 ((8.2b), (8.3) and the proof of Proposition 8.4, pp. 223–224). The construction follows the proof of Proposition 8.4, with the following differences.

- **One translation point, unnormalized labels.** Bernstein–Lapid write \(\mathbf D^{Q,\eta}_a\varphi=a\cdot\varphi-a^{\eta}\varphi\) for \(a\in\mathfrak A_Q\), with the normalized action \(a\cdot\varphi(g)=\delta_Q(a)^{-1/2}\varphi(ag)\) of (6.2). The operators of (8.2b) and (8.3) are products \(\mathbf D^{Q,\underline\eta}_{\underline a}=\prod_i\mathbf D^{Q,\eta_i}_{a_i}\), with an independently varying point \(a_i\in\mathfrak A_Q\) for every entry \(\eta_i\) of the exponent lists (§8.1). The equations here use a single point \(b\) in all factors, the common-point operator \(\mathbf D^{Q,\underline\eta}_b\) of §8.1. They are written with the unnormalized left translation \(T_b\varphi(g)=\varphi(bg)\). Removing the scalar \(\delta_Q(b)^{-1/2}\) from a factor gives \(\delta_Q(b)^{1/2}\mathbf D^{Q,\eta}_b=T_b-\delta_Q(b)^{1/2}b^{\eta}\), whose root \(\delta_Q(b)^{1/2}b^{\eta}=b^{\eta+\rho_Q}\) is \(b\) raised to the unnormalized label \(\eta+\rho_Q\). The labels of the premises (`CompetingWeylExponents`, `HasUnnormalizedExponent`) are unnormalized in this sense. So each polynomial below, evaluated at \(T_b\), is a nonzero scalar multiple of a common-point operator of (8.2b) or (8.3). The conclusion `EisensteinCuspidalTestSystemStatement` is itself stated with one point per polynomial.
- **The homogeneous equations are part of the system.** The system of Bernstein–Lapid consists of the Harish-Chandra equations (8.2a) and the non-homogeneous equations (8.2b). At an arbitrary parameter they deduce (8.3) from (8.2b) by adjoining the identity factors \(w=e\), which are present when \(Q\subset P\). Then \(P_e=Q\), and the identity factors have the exponents \(\underline\mu_Q+\lambda\) of the cuspidal part of \(C_{P,Q}\varphi_\lambda\). So they map \(C_{P,Q}\varphi_\lambda\) into \((\tilde{\mathcal A}^{\mathrm{cusp}}_Q)^\perp\). Here the common-point homogeneous equations (8.3) are included in the system as a second family of equations, so every solution satisfies them by construction. The Harish-Chandra equations (8.2a) are not part of this system. They enter the domination reduction separately.
- **Corollary 6.10.** Bernstein–Lapid use Corollary 6.10 to verify (8.2b) for the Eisenstein series in the regular region. Here Corollary 6.10 enters through premise 2, and it is used only to show that the regular Eisenstein series satisfies both families of equations.
- **Uniqueness.** Once a solution is automorphic, Bernstein–Lapid observe that (8.2b) is equivalent to (6.21), and they conclude by (6.22). Here the common-point non-homogeneous equations give the competing-exponent support of (6.21): every nonzero component of the cuspidal projection of the tested difference carries a competing label. This support is the hypothesis of premise 3.

## The premises

1. `EisensteinStandardizationStatement` (module `AdelicEisensteinStandardizationStatement`). It gives a standard family `fam` with index \(I\), a compact \(K'\) in good position, an archimedean \(t\), finitely many automorphic \(\varphi'_i\) on \(X_{P_I}\), linear forms \(\ell_i\) and a parameter isomorphism \(\iota\). Right translation by \(t\) carries \(K_\infty\)-automorphic forms to \(K'_\infty\)-automorphic forms, regularity is transported, and \(E(\varphi,\lambda)(gt)=\sum_ie^{\ell_i(\lambda)}E'(\varphi'_i,\iota\lambda)(g)\) for regular \(\lambda\).
2. `EisensteinUniformCuspidalExpansionStatement` (module `AdelicEisensteinUniformCuspidalExpansionStatement`): Corollary 6.10 for finite families with uniform competing labels and degree bound.
3. `EisensteinRegularUniquenessStatement` (module `AdelicEisensteinRegularUniquenessStatement`): (6.22) for finite families. Its hypothesis is the competing-exponent support of (6.21): every nonzero component of an exponent decomposition of the cuspidal projection of \(C_Jv-C_{I,J}\Phi\) carries a competing label.
4. `CuspidalProjectionDecompositionStatement` (module `AdelicCuspidalProjectionDecompositionStatement`): unique cuspidal projections of constant terms of automorphic forms, with finite exponent decompositions.
5. `LeviCuspFormPairingMajorantStatement` (module `AdelicLeviCuspFormMajorantStatement`): integrable majorants of the Levi cusp forms against every growth weight (Mœglin–Waldspurger I.2.18). These make the cusp tests continuous on \(\mathfrak F^R_L\) through `constantTermLeviPairingCLM`.
6. `ParameterTwistAutomorphyStatement` (module `AdelicParameterTwistAutomorphyStatement`): \(\varphi_\lambda\) is automorphic on \(X_{P}\) (§2.2).

Premises 2–6 are applied to `fam`, \(I\), \(K'\) and the \(\varphi'_i\). The coefficients are \(a_i(s)=e^{\ell_i(e(s))}\) and the parameter is \(\lambda'(s)=\iota(e(s))\), linear in the coordinates \(s\).

## The data of the system

The standard family of the conclusion is `fam`, and the compact is \(K'\). Iwasawa coverage for every standard parabolic follows from that for the minimal one (`isIwasawaCompact_of_le`, module `AdelicCuspidalTestAlgebra`).

For each standard \(Q\), premise 2 gives competing data `data Q` (Weyl elements \(w\neq1\)) and a degree bound `nexp Q`. For \(Q\le I\), premise 4 gives the cuspidal projections of \(C_Q\varphi'_i\) with exponent decompositions \(\sum_{\mu\in s_{Q,i}}c_{Q,i,\mu}\) and degree bounds \(n_{Q,i,\mu}\). These data do not depend on the parameter.

**Polynomials.** For \(b\in\mathfrak A_Q\):

- `competingTestPolynomial Q` is \(\prod_k\bigl(X-b^{\mathrm{label}_k(\lambda')}\bigr)^{\mathtt{nexp}\,Q+1}\). The competing unnormalized labels of premise 2 take the place of the exponents \(w(\underline\mu_{P_w}+\lambda)\), \(w\neq e\). Evaluated at \(T_b\), it is a nonzero scalar multiple of the common-point operator of (8.2b).
- `cuspidalTestPolynomial Q` multiplies it, for \(Q\le I\), by the identity factors \(\prod_{i,\mu}\bigl(X-b^{\mu+\lambda'|_{P_Q}}\bigr)^{n_{Q,i,\mu}+1}\). Their roots come from the unnormalized exponents of the cuspidal parts of the \(C_{I,Q}\varphi'_{i,\lambda'}\), and they take the place of the exponents \(\underline\mu_Q+\lambda\) of the term \(w=e\). Evaluated at \(T_b\), the product is a nonzero scalar multiple of the common-point operator of (8.3).

Both are monic of a degree that does not depend on \(s\), with nonzero constant coefficient and entire coefficients, since every root is the exponential of an affine function of \(s\) (`differentiable_parameterPower_affine`). The polynomial `D J b Q s` of the conclusion is `cuspidalTestPolynomial Q` at the lift of \(b\in\mathfrak A_J\) to \(\mathfrak A_Q\) (`splitComponentLift`, from `exists_positiveSplitComponent_lift_with_values`), for \(Q\le J\). For \(Q\not\le J\) it is \(X-1\).

**Equations.** The cusp tests are the Levi cusp forms for \(K'_\infty\). The continuous linear form `constantTermLeviPairingCLM` evaluates \(v\mapsto\langle C_Qv,\psi\rangle_g\) on \(\mathfrak F^R_L\); it uses the majorants of premise 5. The index type has two parts.

- **Homogeneous, common-point form of (8.3).** One equation for each \(J\), \(b\in\mathfrak A_J\), \(Q\le J\), cusp test \(\psi\) along \(Q\) and \(g\): \(\sum_kD_k(s)\langle C_Qv,\psi\rangle_{b^kg}=0\).
- **Non-homogeneous, common-point form of (8.2b).** One equation for each \(J\), \(b\in\mathfrak A_J\), cusp test \(\psi\) along \(J\) and \(g\). With \(D^{\mathrm c}\) the competing polynomial:
  \[
  \sum_kD^{\mathrm c}_k(s)\langle C_Jv,\psi\rangle_{b^kg}=\sum_kD^{\mathrm c}_k(s)\bigl\langle C_{I,J}\Phi_s,\psi\bigr\rangle_{b^kgt^{-1}},\qquad \Phi_s=\sum_ia_i(s)\,\varphi'_{i,\lambda'(s)} .
  \]

## Proof of the four properties

- **Analyticity.** The left sides are finite sums of fixed continuous forms with entire coefficients. On the right side, `leviPairing_parabolicConstantTerm_twist_sum_smul` and `leviPairing_constantTerm_parameterTwist` (modules `AdelicEisensteinInducingPairingContinuation` and `AdelicStandardConstantTermTwist`) give \(\langle C_{I,J}\Phi_s,\psi\rangle_h=\sum_ia_i(s)\langle C_J\varphi'_i,\psi\rangle_h\,m_{P_I}(h)^{\lambda'(s)}\) for \(J\le I\), and \(0\) otherwise. Both factors are entire in \(s\).
- **(8.3) for every solution.** The homogeneous equations belong to the system. `translate_mem_cuspidalAnnihilator` turns them into membership of \(D(T_b)C_Qv\) in `cuspidalAnnihilator`. Absolute convergence comes from the majorants (`exists_leviPairing_constantTerm_bound`).
- **The Eisenstein series is a solution at \(R_0\)-regular \(s\).** Let \(s\) be \(R_0\)-regular and let \(v\) be a vector of the chosen stage \(\mathfrak F^R_L\) whose underlying function is \(E(\varphi,e(s))\). Then \(v\) satisfies the equations. The clause says nothing when no such vector exists: the Eisenstein series need not lie in \(\mathfrak F^R_L\) for an arbitrary \(R\). In the domination reduction `eisensteinSystemDomination_of`, the premise `EisensteinCommonGrowthStatement` supplies such a vector for the chosen \(L\) and sufficiently large \(R\).
  By premise 1, \(E(\varphi,e(s))=E_\Sigma(\cdot\,t^{-1})\) with \(E_\Sigma=\sum_ia_iE'(\varphi'_i,\lambda')\). Hence the tested constant terms of \(v\) are those of \(E_\Sigma\) at \(gt^{-1}\) (`constantTerm_mul_right`, `leviPairing_mul_right`). Premise 2, the form of Corollary 6.10 used here, writes them as the tested identity term plus tested competing terms \(\mathrm{terms}_k\) with polynomial orbits of degree \(\le\mathtt{nexp}\).
  - The competing factor of a term kills the term (`isTranslationPolynomialSolution_pow_of_polynomialOrbit`) and then its pairings (`isTranslationPolynomialSolution_leviPairing_of_polynomialOrbit`).
  - For \(Q\le I\), the identity term is a finite sum of pairings of the twisted components \(c_{Q,i,\mu}m_{P_I}^{\lambda'}\). Their exponents are \(\mu+\lambda'|_{P_Q}\) with the same degree bounds (`HasPolynomialOrbit.parameterTwist`), and the identity factors kill them (`isTranslationPolynomialSolution_identityPairing`).
  - So \(D\) kills the tested constant terms of \(v\), which gives the homogeneous equations. \(D^{\mathrm c}\) kills the tested difference, which gives the non-homogeneous ones.
- **Uniqueness at \(R_0\)-regular \(s\).** Let \(v\) be a solution in \(\mathfrak F^R_L\) whose underlying function is automorphic for \(K_\infty\). By premise 1, \(w=v(\cdot\,t)\) is automorphic for \(K'_\infty\). Premise 6 makes \(\Phi_s\) automorphic on \(X_{P_I}\). For every standard \(J\), the non-homogeneous equations at the points \(gt\) say that \(D^{\mathrm c}(T_b)\bigl(C_Jw-C_{I,J}\Phi_s\bigr)\) has vanishing cusp tests.
  - `exists_competing_cuspidalProjection` takes the cuspidal projections of \(C_Jw\) and of \(C_{I,J}\Phi_s\) from premise 4, subtracts them (`IsCuspidalProjection.sub`, `IsExponentDecomposition.sub`, module `AdelicLeadingCuspidalInjectivityReduction`), and applies `exists_eq_of_aeval_mem_cuspidalAnnihilator` (module `AdelicExponentLocalization`). The nonzero components of the difference then carry competing labels. This is the competing-exponent support of (6.21).
  - This support is the hypothesis of premise 3, which gives \(w=\sum_ia_iE'(\varphi'_i,\lambda')\). Translating back by \(t^{-1}\) and using premise 1 gives \(v=E(\varphi,e(s))\).

**The threshold.** \(R_0=\max(R_1,R')\). Here \(R_1\) is the threshold of the comparison in premise 1. \(R'\) is the threshold that premise 1 transports to the bound \(\sum_J|R_2(J)|+|R_3|\), which dominates the thresholds of premises 2 and 3. It depends only on the inducing data, not on the coordinates.

## Implementation notes

The relative Weyl group of the family is finite (`ArthurRelative.finite_relativeWeylGroup`). The closed immersion of `fam.p I` comes from the compatibility of the family. The monomorphism property of the split-component map follows from the factorization `factor_comp` of the compatible presentation. The main proof is a single tactic proof and runs with `maxHeartbeats 800000`.
