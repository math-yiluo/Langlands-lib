# Algebra of the cuspidal tests

Module `Langlands.Global.AdelicCuspidalTestAlgebra`.

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §6.2 ((6.2), (6.3), (6.8)), §8.4 ((8.2b), (8.3), proof of Proposition 8.4, pp. 223–224). Provenance: derived. The module proves elementary facts that Bernstein–Lapid use without separate statements when they write the cuspidal equations (8.2b) and (8.3). They are stated for the common-point form of these equations: one point \(b\) of the positive split component in all factors, and the unnormalized left translation \(T_b\varphi(g)=\varphi(bg)\). All results are proved here.

## Polynomial families with entire coefficients

`IsEntirePolynomialFamily P` says that every coefficient of the polynomial \(P(s)\) is an entire function of the parameter \(s\) in a complex normed space. The family is closed under products (`mul`, `pow`, `prod`, using the formula for the coefficients of a product), contains constants (`const`), and contains \(X-r(s)\) for entire \(r\) (`X_sub_C`).

## Products of powers of linear factors

For a finite set of labels \(I\), roots \(r_i\) and multiplicities \(m_i\), let \(D=\prod_{i\in I}(X-r_i)^{m_i+1}\). Labels with equal roots give separate factors.

- `monic_prod_X_sub_C_pow`: \(D\) is monic.
- `natDegree_prod_X_sub_C_pow`: \(D\) has degree \(\sum_i(m_i+1)\).
- `coeff_zero_prod_X_sub_C_pow_ne_zero`: if no root is zero, \(D(0)\neq0\). The constant coefficient is the product of the \((-r_i)^{m_i+1}\).
- `exists_eq_of_eval_prod_pow_eq_zero`: every zero of \(D\) is one of the \(r_i\).

## Translation polynomials

`IsTranslationPolynomialSolution a D φ` (module `AdelicLocalFinitenessStatement`) is the pointwise equation \(\sum_k D_k\,\varphi(a^kg)=0\). By `isTranslationPolynomialSolution_iff_aeval` (module `AdelicExponentPolynomials`), it says that \(D\) evaluated at the left shift by \(a\) kills \(\varphi\). Hence:

- `IsTranslationPolynomialSolution.of_dvd`: a multiple of an annihilating polynomial annihilates.
- `IsTranslationPolynomialSolution.zero`, `.add`, `.congr`: the solutions of a fixed equation form a space, and the predicate depends only on the values of the function.
- `isTranslationPolynomialSolution_sum_of_dvd`: one polynomial annihilating finitely many functions annihilates every linear combination of them.

## Transfer to Levi pairings

Let \(J\) be standard, \(b\) a point of the positive split component \(\mathfrak A_J\), and \(\psi\) a Levi test. Write \(\langle f,\psi\rangle_g\) for `leviPairing J f g ψ`, the pairing over \(M_J(F)\backslash M_J(\mathbb A)^1\) of (6.8).

- `isTranslationPolynomialSolution_leviPairing`: if \(D\) in the translation by \(b\) annihilates \(f\), and the pairings of \(f\) converge absolutely at every point (`leviPairingDomain`), then \(D\) annihilates \(g\mapsto\langle f,\psi\rangle_g\). The shift by \(b\) moves from \(f\) to the external argument because \(b\) commutes with the Levi (`leviPairingIntegrand_splitComponent`). The pairing is linear on its domain (`leviPairingLinear`).
- `aeval_splitComponentRepresentation_apply` writes \(D\), evaluated at the left translation `splitComponentRepresentation J b`, as the explicit sum \(\sum_k D_k f(b^kg)\). `aeval_mem_leviPairingDomain` shows that this function stays in the pairing domain.
- `leviPairing_sub` is linearity of the pairing for a difference of two absolutely convergent pairings.

## Right translation

For a point \(t\) of \(G(\mathbb A)\), `constantTerm_mul_right` gives \(C_J(f(\cdot\,t))(g)=C_Jf(gt)\). `leviPairingIntegrand_mul_right` and `leviPairing_mul_right` give \(\langle f(\cdot\,t),\psi\rangle_g=\langle f,\psi\rangle_{gt}\). Both follow from associativity inside the defining integrals.

## Iwasawa coverage

`isIwasawaCompact_of_le`: if \(P_Q(\mathbb A)K=G(\mathbb A)\) and \(Q\le P\), then \(P_P(\mathbb A)K=G(\mathbb A)\). The proof maps \(P_Q\) into \(P_P\) by `nestedParabolicHom`.

## Twists

Let \(Q\le I\) and let \(K\) satisfy `hK : IsIwasawaCompact (fam.p I) K`. Write \(m_{P_I}(g)^\lambda\) for `hK.heightPower λ g`.

- `heightPower_splitComponent_mul`: for \(x\in P_Q(\mathbb A)\), \(m_{P_I}(xg)^\lambda=x^{\lambda|_{P_Q}}\,m_{P_I}(g)^\lambda\). The restriction is along `nestedParabolicHom`. The proof combines `IsIwasawaCompact.height_map_mul` with `parameterPower_parameterRestrict`.
- `HasPolynomialOrbit.parameterTwist`: if \(c\) has polynomial orbits of degree at most \(n\) for the exponent \(\mu\) along \(\mathfrak A_Q\) (`HasPolynomialOrbit`), then \(c_\lambda=c\,m_{P_I}^\lambda\) has polynomial orbits of degree at most \(n\) for \(\mu+\lambda|_{P_Q}\). The orbit polynomial at \(g\) is multiplied by the constant \(m_{P_I}(g)^\lambda\).
- `leviPairing_parameterTwist_of_le` and `parameterTwist_mem_leviPairingDomain`: the twist is constant on norm-one Levi orbits (`leviPairingIntegrand_parameterTwist`, module `AdelicStandardConstantTermTwist`), so \(\langle c_\lambda,\psi\rangle_g=\langle c,\psi\rangle_g\,m_{P_I}(g)^\lambda\), and absolute convergence is kept.

## Linear combinations of automorphic functions

`isAutomorphicOn_sum_smul`: a finite linear combination of functions automorphic on a standard parabolic quotient is automorphic there, since these functions form a space (`automorphicFunctionsOn`).

The corresponding facts for differences of cuspidal projections and of exponent decompositions are `IsCuspidalProjection.sub` and `IsExponentDecomposition.sub` in the module `AdelicLeadingCuspidalInjectivityReduction`.
