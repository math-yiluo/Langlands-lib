# From one inducing function to finite families in the uniform cuspidal expansion

Module `Langlands.Global.AdelicEisensteinUniformCuspidalExpansionFamily`. It defines the
proposition `Langlands.Global.EisensteinUniformCuspidalExpansionOneStatement` and proves

`eisensteinUniformCuspidalExpansion_of_one : EisensteinUniformCuspidalExpansionOneStatement.{u} →
EisensteinUniformCuspidalExpansionStatement.{u}`,

with `EisensteinUniformCuspidalExpansionStatement` the statement of module
`AdelicEisensteinUniformCuspidalExpansionStatement` (Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), Corollary 6.10, §6.10,
pp. 207–209, in the norm-one tests (6.8) of §6.2, for finite families with a uniform degree).

## The proposition for one inducing function

Provenance: derived. `EisensteinUniformCuspidalExpansionOneStatement` has the binders of
`EisensteinUniformCuspidalExpansionStatement`, with one automorphic function \(\varphi\) on
\(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\) in place of the family and no coefficients. For
every standard \(J\) it asks for a threshold \(R\), competing data
`data : CompetingWeylExponents fam I J 1` and a degree bound \(n\), such that for every
\(R\)-regular \(\lambda\) there are terms with `fam.HasPolynomialOrbit J (data.label k λ) n`
and, for every Levi cusp form `test` on \(M_J\) and every \(g\):

1. each tested term is absolutely integrable on the norm-one rational quotient of \(M_J\);
2. the integrands of \(\langle C_JE(\varphi,\lambda),\texttt{test}\rangle_g\) and of
   \(\langle C_{I,J}\varphi_\lambda,\texttt{test}\rangle_g\) are absolutely integrable;
3. \(\langle C_JE(\varphi,\lambda),\texttt{test}\rangle_g-\langle C_{I,J}\varphi_\lambda,
   \texttt{test}\rangle_g=\sum_k\langle\texttt{terms}\ k,\texttt{test}\rangle_g\).

Items 1 and 3 are the case \(m=1\), \(a_0=1\) of the finite-family statement. Item 2 is the
absolute convergence of both pairings, applied to the constant terms of \(E(\varphi,\lambda)\)
and of \(\varphi_\lambda\). Bernstein–Lapid define the pairing (6.8) with cusp forms on
\(M(F)\backslash M(\mathbb A)^1\) whenever the integral converges absolutely, and item 2 makes
that convergence part of the statement.

## The proof

Fix the data of the finite-family statement, the functions \(\varphi_0,\dots,\varphi_{m-1}\) and
\(J\).

1. For each \(i\), the one-function proposition gives \(R_i\), `data i` and \(n_i\), and
   `eisensteinAbsoluteConvergence` (module `AdelicEisensteinConvergenceProof`) gives a
   convergence threshold \(R'_i\) for \(\varphi_i\). Put \(R_0=\sum_i(|R_i|+|R'_i|)\), which bounds
   every \(R_i\) and \(R'_i\), take the concatenated labels `CompetingWeylExponents.sigma data`
   and \(n_0=\max_in_i\) (`Finset.univ.sup n`). These depend only on the family and on \(J\).
2. Let \(\lambda\) be \(R_0\)-regular; it is then \(R_i\)- and \(R'_i\)-regular for every \(i\)
   (the regularity condition is a strict lower bound). Let \(a_i\) be arbitrary. For each \(i\)
   take the terms \(T_{i,j}\) of \(\varphi_i\) at \(\lambda\). The term of index \(k\) of the family
   is \(a_i\,T_{i,j}\), with \((i,j)\) the image of \(k\) under the inverse of
   `finSigmaFinEquiv`. Its label is that of \(T_{i,j}\) (`CompetingWeylExponents.sigma_label`),
   and it has degree at most \(n_0\) by `hasPolynomialOrbit_of_degree_le` and
   `hasPolynomialOrbit_const_mul`. Its tested integrand is \(a_i\) times that of \(T_{i,j}\).
3. Constant terms. Each \(E(\varphi_i,\lambda)\) is continuous: with a linear chart
   (`exists_complexParameterEquiv`) and the compact parameter set \(\{\lambda\}\), the
   convergence statement bounds its terms on every compact set by a summable sequence, and
   `continuous_eisensteinSeries_of_compactBound` applies. It is left \(G(F)\)-invariant
   (`eisensteinSeries_leftRationalInvariant`). Hence
   \(C_J(\sum_ia_iE(\varphi_i,\lambda))=\sum_ia_iC_JE(\varphi_i,\lambda)\)
   (`integrable_constantTermIntegrand_of_rationalInvariant`, `constantTerm_finset_sum`). For
   the twists, \(C_{I,J}(\sum_ia_i\varphi_{i,\lambda})=\sum_ia_iC_{I,J}\varphi_{i,\lambda}\) by
   `integrable_constantTermIntegrand_parameterTwist` and `parabolicConstantTerm_finset_sum`,
   using the continuity and invariance contained in the automorphy of \(\varphi_i\).
4. Pairings. By item 2 for each \(\varphi_i\), `leviPairing_finsetSum` splits both tested
   constant terms into \(\sum_ia_i\) times those of the \(\varphi_i\). Item 3 for each \(\varphi_i\)
   turns the difference into \(\sum_ia_i\sum_j\langle T_{i,j},\texttt{test}\rangle_g
   =\sum_{i,j}\langle a_iT_{i,j},\texttt{test}\rangle_g\) (`leviPairing_const_mul`). Reindexing the
   double sum through `Fintype.sum_sigma` and `finSigmaFinEquiv` gives the sum over the
   concatenated labels.

No hypothesis of the finite-family statement is added, the universe \(u\) is kept, and the
one-function proposition is used at the same universe.
