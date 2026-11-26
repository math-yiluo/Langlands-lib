# Uniqueness of convergent Eisenstein series from their cuspidal components

Module `Langlands.Global.AdelicEisensteinRegularUniquenessStatement`. It contains one statement, `Langlands.Global.EisensteinRegularUniquenessStatement`, and no proof.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`):
  - §6.10, the conditions (6.21) and the uniqueness assertion (6.22), p. 209;
  - Theorem 6.3, leading cuspidal components, §6.3;
  - Corollary 6.10;
  - their use in the proof of Proposition 8.4, §8.4, pp. 223–224.

Provenance: derived. In Bernstein–Lapid, (6.21) is the condition, for every standard \(Q\),
\[
C^{\mathrm{cusp}}_{G,Q}\psi-C^{\mathrm{cusp}}_{P,Q}\varphi_\lambda\in\mathcal A^{\mathrm{cusp}}_Q\Bigl(\textstyle\bigvee_{w\in W^{\supset Q}(P)\setminus\{e\}}w\bigl(\underline\mu^{\mathrm{cusp}}_{P_w}+\tilde\lambda\bigr)\Bigr).
\]
Here \(\bigvee\) concatenates the exponent lists, keeping repetitions, and \(\mathcal A^{\mathrm{cusp}}_Q(\underline\nu)\) is a single space attached to the concatenated list. By (6.14) and the polynomial exponential spaces on p. 206, the polynomial degree attached to each exponent is at most its number of repetitions minus one. The source exponents are normalized. They become raw (unnormalized) exponents by adding \(\rho_Q\), as in (6.2) and (6.10). Bernstein–Lapid then state (6.22): for \(\langle\operatorname{Re}\lambda,\alpha^\vee\rangle\gg0\), \(E(\varphi,\lambda)\) is the unique automorphic form satisfying (6.21).

The hypothesis of the statement here is deliberately weaker than (6.21):

- it uses the Library's cuspidal projection (the norm-one Levi tests of (6.8)) and an exponent decomposition of that projection;
- it records only the **support**: every nonzero component carries a raw exponent among the competing affine labels of `CompetingWeylExponents` (module `AdelicConvergentCuspidalTestExpansionStatement`);
- it allows any finite polynomial degree for each component, so the multiplicity bound of (6.14) is not imposed.

The conclusion is that of (6.22), and the leading-component argument below uses only this support information. In particular, (6.21), converted to raw exponents, implies the hypothesis here, so the statement contains the uniqueness assertion (6.22).

## Statement

The binders are those of the published `ConvergentCuspidalTestExpansionStatement` (module `AdelicConvergentCuspidalTestExpansionStatement`), without its second index, its Weyl representative and its Levi conjugation:

- a number field \(F\);
- an affine group scheme \(G\) of finite type;
- a compatible standard family `fam` with an inducing index \(I\);
- a maximal compact \(K\) with `hK : IsIwasawaCompact (fam.p I) K`, Iwasawa coverage for the minimal standard parabolic, and maximal compact intersections with the standard Levis;
- a closed matrix embedding `rho` and the smooth structure `hsmooth`.

Automorphy is taken for the archimedean part \(K_\infty\) of \(K\) and the canonical commutator datum `adelicDifferentialCommutator_of_smooth`. Fix finitely many functions \(\varphi_0,\dots,\varphi_{n-1}\) automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\). Fix also data `data J : CompetingWeylExponents fam I J 1` for every standard \(J\). These are competing labels \(\mathrm{label}_k(\lambda)\), affine in \(\lambda\), of Weyl elements \(w_k\neq1\) that send the simple roots of \(I\) to positive roots.

Then there is \(R\) with the following property. Let \(\lambda\) be \(R\)-regular, let \(a_0,\dots,a_{n-1}\in\mathbb C\) be arbitrary, and let \(v\) be automorphic on \(G(F)\backslash G(\mathbb A)\). Write \(\varphi_{i,\lambda}\) for `hK.parameterTwist (φ i) λ`. Assume that for every standard \(J\):

- the function \(C_Jv-C_{I,J}\bigl(\sum_ia_i\varphi_{i,\lambda}\bigr)\) has a cuspidal projection `vc` along \(J\) (`fam.IsCuspidalProjection`);
- `vc` has an exponent decomposition \(\sum_{\mu\in s}c_\mu\) (`fam.IsExponentDecomposition`) whose nonzero components all carry competing labels: \(c_\mu\neq0\Rightarrow\mu=\mathrm{label}_k(\lambda)\) for some \(k\).

Then \(v=\sum_ia_iE(\varphi_i,\lambda)\), where \(E(\varphi_i,\lambda)\) is `hK.eisensteinSeries (φ i) λ`.

**Uniformity.** The threshold \(R\) depends on the family \((\varphi_i)\) and on `data`, but not on the coefficients \(a_i\). For \(n=1\) and \(a_0=1\) this is the uniqueness assertion (6.22) for \(\varphi=\varphi_0\). The uniform form is needed where the inducing function itself depends on \(\lambda\) through finitely many entire coefficients. For example, `EisensteinFiniteCompactChangeStatement` (module `AdelicEisensteinFiniteCompactChangeStatement`) writes the twist for one Iwasawa compact as \(\sum_v e^{\langle\lambda,v\rangle}\) times the twists of finitely many fixed functions for another compact.

Here \(C_J\) is `fam.constantTerm J`, and \(C_{I,J}\) is `fam.parabolicConstantTerm I J`, which is \(0\) unless \(J\le I\). This matches the absence of the affine term in (6.21) for \(Q\not\subseteq P\).

## Why it holds

This explains the truth of the statement; the module contains no proof. Let \(\lambda\) be \(R\)-regular.

1. **Competing labels are not leading.** The real part of \(\mathrm{label}_k(\lambda)\) is \(w_k(\operatorname{Re}\lambda)\) plus a fixed shift (field `ambient`). Here \(w_k\neq1\) sends the simple roots of \(I\) to positive roots. By the separation of shifted Weyl translates of regular parameters from the leading chamber (`eisensteinAmbientWeylSeparation`, module `AdelicEisensteinWeylSeparation`), no such label is a leading exponent once \(R\) is large for the finitely many shifts of `data`, and the same holds for the shifts of step 2.
2. **Reduction to one inducing function.** Put \(\varphi=\sum_ia_i\varphi_i\). It is automorphic on \(U_I(\mathbb A)M_I(F)\backslash G(\mathbb A)\), with \(\varphi_\lambda=\sum_ia_i\varphi_{i,\lambda}\). In the region of absolute convergence, \(E(\varphi,\lambda)=\sum_ia_iE(\varphi_i,\lambda)\). The cuspidal exponents of the constant terms of \(\varphi\) lie in the finite union of those of the \(\varphi_i\). So the competing exponents of \(E(\varphi,\lambda)\) in Corollary 6.10 have real parts \(w(\operatorname{Re}\lambda)\) plus shifts from a finite set that does not depend on the \(a_i\).
3. **Leading components of \(v\).** The cuspidal projection of \(C_Jv\) is `vc` plus the cuspidal projection of \(C_{I,J}\varphi_\lambda\). Its leading part is therefore the leading part of the cuspidal projection of \(C_{I,J}\varphi_\lambda\).
4. **Leading components of \(E\).** In the region of absolute convergence, Corollary 6.10 and Lemma 6.8 give the same leading part for the Eisenstein series \(E(\varphi,\lambda)\), which is automorphic there. The published `ConvergentCuspidalTestExpansionStatement` states the corresponding scalar comparison in the norm-one Levi tests.
5. **Conclusion.** \(v\) and \(E(\varphi,\lambda)\) have the same leading cuspidal components, so they are equal by Theorem 6.3 (`LeadingCuspidalInjectivityStatement`). This is why \(K\) is assumed in good position, as in that statement.

## Use

The statement is intended as the source of clause 4 of `EisensteinCuspidalTestSystemStatement` (module `AdelicEisensteinCuspidalTestSystemStatement`). For an automorphic solution \(v\) of the cuspidal tests (8.2b), the proof of Proposition 8.4 shows that (8.2b) is equivalent to (6.21). The difference operators in (8.2b) annihilate the cuspidal projection of \(C_Jv-C_{I,J}\varphi_\lambda\). Their roots are the values of the competing raw exponents. So every nonzero component of an exponent decomposition of that projection carries a competing label. This is the hypothesis here, and the statement then gives \(v=E(\varphi,\lambda)\). The finite-family form allows the inducing function to be a combination of fixed functions with \(\lambda\)-dependent coefficients, as after a change of Iwasawa compact.
