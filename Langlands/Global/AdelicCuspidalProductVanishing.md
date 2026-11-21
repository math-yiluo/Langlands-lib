# Products of split-component differences killed by the vanishing criterion

This module formalizes one step in the proof of Lemma 8.1 of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §8.1, p. 222. The step is "By (8.1), for any \(\phi\in V\) we have \(\big(\prod_{Q\subset P}\Delta^{P,\underline\lambda_Q}_{\underline a_Q}\big)C_{G,P}\phi\equiv0\)" (cf. Mœglin–Waldspurger I.3.5). The proof is **conditional** on the vanishing criterion (8.1), in the continuous fibrewise formulation of the published proposition `ParabolicCuspidalVanishingStatement`, which enters as the hypothesis `hvan`. That formulation asks for continuity and a moderate growth bound for the function itself (no derivatives), and it replaces the cutoff tests \((\tilde{\mathcal A}^{\mathrm{cusp}}_Q)^\perp\) of (8.1) by the fibrewise tests of BL (6.8): pairings against Levi cusp forms on the norm-one rational quotient of \(M_Q\), at every right translate. The module does not prove (8.1).

## Main theorem

`StandardParabolicFamily.aeval_prod_adelicLeftShift_constantTerm_eq_zero` has the following hypotheses:

- `hvan : ParabolicCuspidalVanishingStatement`;
- a maximal compact subgroup \(K\) that is an Iwasawa compact for every member of the standard family;
- a matrix representation \(\rho\) of size \(N>0\) with `IsClosedSubgroup rho`;
- a standard parabolic \(P\) and a continuous left \(G(F)\)-invariant function \(f\) (`ContinuousRationalFunctions`) of moderate growth;
- one positive point \(a\) of the split component \(A_P\), with raw left shift \(L_a\varphi=\varphi(a\,\cdot)\) (`adelicLeftShift`);
- a finite set \(S\) of standard indices containing every \(Q\le P\), and complex polynomials \(D_Q\).

Assume that for every \(Q\le P\) the function \(D_Q(L_a)\,C_Q f\) lies in `cuspidalAnnihilator Q`, for the infinite part of \(K\). This is the fibrewise annihilator of `AdelicCuspidalAnnihilator`: absolutely convergent zero pairings against all Levi cusp forms, at every right translate. Then
\[
\Big(\prod_{Q\in S}D_Q\Big)(L_a)\;C_P f=0 .
\]
Every factor uses the **same** point \(a\in A_P\), and factors for indices not below \(P\) are allowed. The polynomials \(D_Q\) are arbitrary. The rest of this section explains how BL's factors are such polynomials; the Lean proof does not use these comparisons.

**BL's difference operators as polynomials in the raw shift.** BL (6.2), p. 201, normalizes the action of \(A_P\) by \(a\cdot\varphi=\delta_P(a)^{-1/2}\varphi(a\,\cdot)\), and §8.1 defines \(\Delta^{P,\lambda}_a\varphi=a\cdot\varphi-a^{\lambda}\varphi\). In the raw shift \(X=L_a\) this operator is the polynomial
\[
\delta_P(a)^{-1/2}X-a^{\lambda}=\delta_P(a)^{-1/2}\big(X-a^{\lambda+\rho_P}\big),\qquad a^{\rho_P}=\delta_P(a)^{1/2}.
\]
It is a nonzero constant multiple of the monic factor with root \(a^{\lambda+\rho_P}\). Nonzero constant factors change neither membership in a subspace nor vanishing, so either form can be used. By `unnormalizedExponentDifference_eq_adelicLeftShift`, the raw difference of `AdelicExponentPolynomials` with parameter \(\mu\) is \(L_{p(a)}\) minus the scalar \(a^{\mu}\), the monic factor with root \(a^{\mu}\). It is the monic form above when \(a^{\mu}=a^{\lambda+\rho_P}\).

**The \(Q\)-level hypotheses.** For \(Q\le P\), BL's hypothesis concerns \(\Delta^{Q,\mu}_b\,C_Q\varphi\) for points \(b\) of \(A_Q\) and exponents \(\mu\) of \(Q\). Let \(b\) be the positive point of \(A_Q\) with the same image in \(G(\mathbb A)\) as \(a\) (`exists_positiveSplitComponent_lift_with_values` in `AdelicNestedSplitComponents`). Then \(L_b=L_a\), and \(\Delta^{Q,\mu}_b\) is the polynomial \(\delta_Q(b)^{-1/2}X-b^{\mu}\) in \(X=L_a\). Its half-modulus is that of \(P\): the Lie algebra of \(U_Q\) is that of \(U_P\) plus that of \(U_Q\cap M_P\), and the common image is central in \(M_P\), so it acts trivially on the second summand and \(\delta_Q(b)=\delta_P(a)\). The value \(b^{\mu}\) depends only on the restriction of \(\mu\) to \(A_P\), as BL remark in §8.1. For a parameter \(\lambda\) of \(P\), `AdelicNestedSplitComponents` proves \(b^{\lambda|_Q}=a^{\lambda}\) for its restriction to \(Q\); the modulus comparison is not formalized. Hence BL's \(Q\)-level hypothesis, applied to tuples whose entries all equal \(b\), is `hD` with \(D_Q=\prod_i\big(\delta_P(a)^{-1/2}X-b^{\mu_{Q,i}}\big)\). The conclusion is then BL's product \(\prod_{Q\subseteq P}\Delta^{P,\underline\mu_Q}_a\,C_P\varphi=0\) with all points equal to \(a\). BL's version for arbitrary tuples \(\underline a_Q\) of different points is not stated here.

## Proof as implemented

Write \(\psi=(\prod_S D_Q)(L_a)\,C_Pf\). The theorem applies `hvan` to \(\psi\) and checks its two hypotheses.

**Moderate growth on the parabolic quotient.** `parabolicModerateSubmodule P` is the complex subspace of functions that are left invariant by \(U_P(\mathbb A)\) and by the image of \(M_P(F)\) (`IsParabolicGeneratorInvariant`), are continuous, and have polynomial growth in the submultiplicative height (`HasHeightGrowth`, with nonnegative constant and exponent).

- `hasModerateGrowthFunction_iff_hasHeightGrowth` compares this growth with the Library's `HasModerateGrowthFunction`. The source norm is a fixed positive multiple of the height, and the height is at least one, so the exponent can be made nonnegative.
- `IsParabolicGeneratorInvariant.isLeftInvariantUnder` passes to the Library's `parabolicQuotientSubgroup`, the join of the two images: the left stabilizer of a function is a subgroup (`scalarLeftStabilizer`).
- `adelicLeftShift_mem_parabolicModerateSubmodule` shows that the subspace is stable under \(L_{p(a)}\). For \(U_P(\mathbb A)\) this is the existing `IsRadicalInvariant.unnormalizedAction`. For \(M_P(F)\), `commute_positiveSplitComponent_levi` shows that the image of a positive point of \(A_J\) commutes in \(G(\mathbb A)\) with the image of every adelic point of \(M_J\). This uses centrality of the specified split component in the Levi. Height growth is preserved by submultiplicativity, \(H(xg)\le H(x)H(g)\).
- `constantTerm_mem_parabolicModerateSubmodule` shows that \(C_Pf\) is in the subspace:
  - \(U_P(\mathbb A)\)-invariance is `isRadicalInvariant_constantTerm`.
  - \(M_P(F)\)-invariance follows from `normalizedConstantTerm_rationalNormalizer_mul`, since the Levi normalizes the radical (`radical_isNormalizedBy_levi`). The rational point is transported by the principal-map naturality.
  - Continuity is `continuous_normalizedConstantTerm`.
  - For growth, `exists_le_of_compactSpace_leftCosetSpace` (an open-cover argument on the compact quotient \(U_P(F)\backslash U_P(\mathbb A)\)) gives \(B\) such that every coset has a representative of height at most \(B\). Since \(f\) is left \(G(F)\)-invariant, each integrand value is bounded by \(C B^r H(g)^r\), and the quotient measure is a probability measure.

  Polynomials in \(L_a\) preserve the subspace (`aeval_apply_mem_of_mapsTo`), so \(\psi\) satisfies `IsModerateContinuousOnParabolic`.

**Cuspidal tests along \(Q\le P\).**

- `constantTerm_aeval_adelicLeftShift` proves \(C_Q\big(D(L_a)h\big)=D(L_a)\,C_Q h\) for every polynomial \(D\), on `radicalIntegrableSubmodule Q P`: \(U_P(\mathbb A)\)-invariant inputs whose \(Q\) constant-term integrand is integrable at every point. The submodule is stable under \(L_{p(a)}\) by the pointwise commutator identity of `AdelicConstantTermSplitComponent`. On it, \(C_Q\) is additive (Bochner integral of integrable functions) and homogeneous. It commutes with \(L_{p(a)}\) by `constantTerm_unnormalizedAction_of_radicalInvariant`. The abstract step is `map_aeval_of_intertwines`, by induction on the polynomial.
- The input \(C_Pf\) lies in that submodule by `isRadicalInvariant_constantTerm` and `hasIntegrableConstantTerm_constantTerm_of_le`. Transitivity `constantTerm_constantTerm_of_le` gives \(C_Q\psi=(\prod_S D)(L_a)\,C_Qf\).
- Write \(\prod_S D=\big(\prod_{S\setminus\{Q\}}D\big)\cdot D_Q\), so \(C_Q\psi=\big(\prod_{S\setminus\{Q\}}D\big)(L_a)\big(D_Q(L_a)C_Qf\big)\).
- `aeval_adelicLeftShift_mem_cuspidalAnnihilator` shows that polynomials in \(L_{p(a)}\) preserve `cuspidalAnnihilator Q`. By `exists_positiveSplitComponent_lift_with_values` of `AdelicNestedSplitComponents`, \(p(a)\) is also the image of a positive point \(b\) of \(A_Q\). Since \(b\) is central in \(M_Q\), the pairing integrand of \(L_{p(b)}h\) at \(g\) equals that of \(h\) at \(p(b)g\) (`InCuspidalAnnihilator.adelicLeftShift`), and the annihilator quantifies over all right translates.

Hence `hvan` applies to \(\psi\), giving \(\psi=0\).

## Dependencies

The module imports the published pairs `AdelicConstantTermSplitComponent` (and through it `AdelicConstantTermTransitivity`, `AdelicExponentPolynomials` and `CompactQuotientSubgroupAverage`), `AdelicNestedSplitComponents` and `AdelicCuspidalAnnihilator`. It also imports the published `AdelicRepresentationHeightPropernessProof` for continuity of the height.
