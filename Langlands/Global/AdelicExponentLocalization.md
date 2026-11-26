# Localization of exponents by difference equations

Module `Langlands.Global.AdelicExponentLocalization`.

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024). In the proof of Proposition 8.4 (§8.4, pp. 223–224), the module is used to recover the competing-exponent support of (6.21) from the affine cusp tests (8.2b), once the solution is known to be automorphic. The exponents are those of the spaces \(\mathcal A_{P,\lambda}\) of (6.3) and (6.10). The provenance is derived: Bernstein–Lapid use the facts proved here without separate statements. The results are elementary linear algebra and group theory, applied to the unnormalized action of the positive split component.

## Abstract results (namespace `Langlands.HarishChandraSchwartz`)

Let \(A\) be a commutative group acting on a complex vector space \(Y\) through \(T:A\to\operatorname{End}(Y)\). Let `jointGenEigenspace T χ` be the joint generalized eigenspace of a function \(\chi:A\to\mathbb C\) (module `ExponentDecomposition`).

- `eq_zero_of_aeval_apply_eq_zero_of_mem_maxGenEigenspace`: if \(D(\mu)\neq0\), then \(D(f)\) is injective on the generalized eigenspace of \(f\) for \(\mu\).
  *Proof.* \((X-\mu)^k\) and \(D\) are coprime, because \(X-\mu\) is irreducible and does not divide \(D\). Take \(aD+b(X-\mu)^k=1\) with \((f-\mu)^ky=0\). Then \(y=a(f)D(f)y\).
- `commute_aeval_jointFamily`: every \(T(a)\) commutes with every polynomial in \(T(b)\). The proof is induction on the polynomial.
- `eval_eq_zero_of_aeval_sum_eq_zero`: let \(c_i\in Y_{\chi_i}\), \(i\in s\), with \(i\mapsto\chi_i\) injective. Suppose that for every \(a\) the polynomial \(D_a\) satisfies \(D_a(T(a))\sum_{i\in s}c_i=0\). Then \(D_a(\chi_i(a))=0\) for every \(a\) and every \(i\) with \(c_i\neq0\).
  *Proof.* \(D_a(T(a))\) preserves each \(Y_{\chi_i}\) (`mapsTo_jointGenEigenspace_of_commute`). By independence of these spaces (`iSupIndep_jointGenEigenspace`), each \(D_a(T(a))c_i\) vanishes. The first result applies, since \(Y_{\chi_i}\) is contained in the generalized eigenspace of \(T(a)\) for \(\chi_i(a)\).
- `exists_eq_one_of_forall_exists_eq_one`: let \(A\) be divisible, and let \(\psi_k\), \(k\in t\), be finitely many homomorphisms from \(A\) to a group such that at every point one of them takes the value \(1\). Then one of them is trivial.
  *Proof.* The kernels cover \(A\), so one of them has finite index by B. H. Neumann's lemma (`Subgroup.exists_finiteIndex_of_leftCoset_cover`). Every \(x=y^m\) with \(m\) that index lies in it (`Subgroup.pow_index_mem`).

## Results for a standard parabolic family (namespace `Langlands.Global.StandardParabolicFamily`)

Let `𝓕` be a `StandardParabolicFamily` and \(J\) a standard index. The positive split component \(\mathfrak A_J\) (`positiveSplitComponent J`) is commutative (`positiveSplitComponent_mul_comm`); a local instance records this. It acts on functions on \(G(\mathbb A)\) by `splitComponentRepresentation J`, that is, by the unnormalized left translation \(T_bf=f(b\,\cdot)\).

- `exists_pow_eq_positiveSplitComponent`: \(\mathfrak A_J\) is divisible. A point of \(\mathfrak A_J\) is the image of a point \(a'\) of the intrinsic positive subgroup of the split torus \(A_J\). The published `PositiveRealTorus.positiveLogEquiv` identifies that subgroup with the real vector space `RealCharacterDual`, so \(a'\) has an \(n\)-th root there. Its image in \(\mathfrak A_J\) is an \(n\)-th root of the given point.
- `exists_eq_of_aeval_splitComponent_sum_eq_zero_of_mem`: the same localization for functions given as joint generalized eigenvectors of \(b\mapsto b^\mu\), rather than by the polynomial orbit condition. The other two results are derived from it.
- `exists_eq_of_aeval_splitComponent_sum_eq_zero` (**localization of exponents**). Assume:
  - \(\sum_{\mu\in s}c_\mu\) is a finite sum of functions on \(G(\mathbb A)\), and each \(c_\mu\) has unnormalized exponent \(\mu\) along \(\mathfrak A_J\) (`HasUnnormalizedExponent`);
  - for every \(b\in\mathfrak A_J\), the polynomial \(D_b\) in the translation by \(b\) annihilates the sum;
  - every root of \(D_b\) is \(b^{\nu_k}\) (`parameterPower`) for some \(k\in t\).

  Then every nonzero \(c_\mu\) has \(\mu=\nu_k\) for some \(k\in t\).

  *Proof.* The functions \(c_\mu\) lie in the joint generalized eigenspaces of the characters \(b\mapsto b^\mu\) (`mem_jointGenEigenspace_of_hasUnnormalizedExponent`). These characters are pairwise distinct, because \(\mu\mapsto(b\mapsto b^\mu)\) is injective on \(\mathfrak A_J\) (second part of the published `eisensteinPositiveParameters`). By the abstract result, for each nonzero \(c_\mu\) and each \(b\), the value \(b^\mu\) is a root of \(D_b\), hence equals \(b^{\nu_k}\) for some \(k\). The characters \(b\mapsto b^{\nu_k-\mu}\) then satisfy the covering hypothesis on the divisible group \(\mathfrak A_J\). One of them is trivial, so \(\nu_k=\mu\) by injectivity.

- `leviPairing_aeval_splitComponent`: for \(f\) whose pairing integrands against a fixed Levi test are integrable at every external argument (`leviPairingDomain`), the Levi pairing of \(D(T_b)f\) at \(g\) is \(D(T_b)\) applied to the function \(g\mapsto\langle f,\psi\rangle_g\).
  *Proof.* Expand \(D(T_b)=\sum_i D_i T_b^i\) and use \(T_b^i=T_{b^i}\). Each translate stays in the pairing domain (`splitComponent_mem_leviPairingDomain`). The pairing is linear there (`leviPairingLinear`), and translation by \(b\in\mathfrak A_J\), which is central in the Levi, moves to the external argument (`leviPairingIntegrand_splitComponent`).
- `exists_eq_of_leviPairing_aeval_eq_zero` (**localization in cusp tests**). Assume:
  - against a fixed Levi test \(\psi\), \(f\) has the same pairings as \(\sum_{\mu\in s}c_\mu\), with \(c_\mu\) of unnormalized exponent \(\mu\);
  - for every \(b\), the pairings of \(D_b(T_b)f\) vanish, and every root of \(D_b\) is some \(b^{\nu_k}\).

  Then every \(c_\mu\) whose pairings with \(\psi\) are not all zero has \(\mu=\nu_k\) for some \(k\).
  *Proof.* The functions \(g\mapsto\langle c_\mu,\psi\rangle_g\) lie in the joint generalized eigenspaces of \(b\mapsto b^\mu\) (`leviPairingLinear_mem_jointGenEigenspace`), and they sum to \(g\mapsto\langle f,\psi\rangle_g\). By the previous result, \(D_b(T_b)\) annihilates this sum. The joint-eigenspace form of the localization then applies. In the application, \(f=C_Jw-C_{I,J}\Phi_s\) is the difference between the constant term of the solution and the constant term of the inducing twist, and \(D_b\) is the competing polynomial of the common-point form of (8.2b). The vanishing of the pairings is then membership of \(D_b(T_b)f\) in the cuspidal annihilator (`InCuspidalAnnihilator`). Equation (8.3) supplies the homogeneous constraints used for automorphy and domination in §8.4, not this localization.

## Detection by cusp tests, from the cuspidal projection statement

The following three results take the published proposition `CuspidalProjectionDecompositionStatement` (module `AdelicCuspidalProjectionDecompositionStatement`) as an explicit hypothesis `hproj`; this module does not prove it. They also assume the setting of that proposition: a maximal compact \(K\) with Iwasawa coverage for the minimal standard parabolic and maximal compact intersections with the standard Levis. Automorphy and cusp forms are taken for the archimedean part of \(K\).

- `mem_leviPairingDomain_of_isAutomorphicOn`: an automorphic function \(\varphi\) on \(U_J(\mathbb A)M_J(F)\backslash G(\mathbb A)\) has absolutely convergent pairings with every Levi cusp form at every point. It is its own constant term along \(J\) (`constantTerm_eq_self_of_automorphicOn`), and the cuspidal projection supplied by `hproj` includes this integrability.
- `eq_zero_of_isCuspidalAlong_of_leviPairing_eq_zero`: a cuspidal automorphic function on \(U_J(\mathbb A)M_J(F)\backslash G(\mathbb A)\) whose Levi cusp pairings all vanish (with absolute convergence) is zero. Both the function and \(0\) are cuspidal projections of its constant term along \(J\), so they agree by the uniqueness clause of `hproj`.
- `exists_eq_of_aeval_mem_cuspidalAnnihilator` (**from difference equations to the support of exponents**). Assume:
  - \(v_c\) is a cuspidal projection of \(f\) along \(J\), with an exponent decomposition \(\sum_{\mu\in s}c_\mu\);
  - for every \(b\in\mathfrak A_J\), \(D_b(T_b)f\) lies in the cuspidal annihilator along \(J\) (`cuspidalAnnihilator`);
  - every root of \(D_b\) is some \(b^{\nu_k}\).

  Then every nonzero \(c_\mu\) has \(\mu=\nu_k\) for some \(k\).
  *Proof.* Fix a Levi cusp form \(\psi\). The pairings of \(f\) are those of \(v_c\), hence the sum of the pairings of the \(c_\mu\), which converge by the first result. If \(\mu\) were none of the \(\nu_k\), the localization in cusp tests would make every pairing of \(c_\mu\) vanish, for every \(\psi\). The second result would then give \(c_\mu=0\).

  In the proof of Proposition 8.4 this recovers, after automorphy, the competing-exponent support of (6.21) from the affine cusp tests (8.2b), in the support form used by `EisensteinRegularUniquenessStatement`. It is applied to \(f=C_Jw-C_{I,J}\Phi_s\), with \(D_b\) the competing polynomial of the common-point form of (8.2b).

The roots may repeat, so the polynomials may have multiple roots. This is the form of the common-point difference operators of Bernstein–Lapid (8.2b) and (8.3) (one point \(b\) in all factors, §8.1), written with the unnormalized translation \(T_b\) and unnormalized labels, with exponent lists that may contain repetitions.
