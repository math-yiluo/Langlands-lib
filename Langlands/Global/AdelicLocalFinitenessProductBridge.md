# Equations of Ξ_main from the product step of Lemma 8.1

Source: Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), proof of Lemma 8.1, §8.1, pp. 221–222, together with the definition of the system Ξ_main in §7.2, pp. 211–212. In that proof, (8.1) gives \(\big(\prod_{Q\subset P}\Delta^{P,\underline\lambda_Q}_{\underline a_Q}\big)C_{G,P}\phi\equiv0\). The space \(V\) is then finite-dimensional by Theorem 7.2. To apply Theorem 7.2 these vanishing identities must be equations of Ξ_main: difference equations for left translation applied to the constant term along the radical of a maximal parabolic \(P_\alpha\) (the constant-term equations), or to the function itself (the central equations). This module makes that translation for the product step `aeval_prod_adelicLeftShift_constantTerm_eq_zero` of `AdelicCuspidalProductVanishing`.

Everything here is **conditional** on the vanishing criterion (8.1), the published `ParabolicCuspidalVanishingStatement`, which enters as the hypothesis `hvan`. The module does not prove (8.1). It also does not construct the polynomials \(D_Q\), prove the cuspidal-annihilator hypotheses `hD`, or show that the group data of Ξ_main (`IsLocalFinitenessGroupData`) consist of images of positive split-component points. These remain inputs.

## Translation lemmas

- `adelicLeftShift_pow_apply`: the \(k\)-th power of the raw left shift \(L_x\varphi=\varphi(x\,\cdot)\) is \(\varphi\mapsto\varphi(x^k\,\cdot)\), by induction on \(k\).
- `aeval_adelicLeftShift_apply` and `isTranslationPolynomialSolution_iff_aeval_adelicLeftShift`: `IsTranslationPolynomialSolution x D φ`, the pointwise equation \(\sum_k D_k\,\varphi(x^k g)=0\) used in `LocalFinitenessData.solutions`, holds if and only if \(D(L_x)\varphi=0\). The proof expands `Polynomial.aeval` as a finite sum over the coefficients. (`AdelicExponentPolynomials` has the same equivalence written with `GroupAction.leftFunctions x⁻¹`.)
- `subgroupConstantTerm_congr_range`: the constant term along a closed subgroup depends only on the image subgroup functor. The definition uses the subgroup only through that image; after generalizing over equal images, both sides agree by reflexivity.
- `StandardParabolicFamily.subgroupConstantTerm_eq_constantTerm`: if a closed subgroup \(u\) has image `standardUnipotent 𝓕.i 𝓕.ν J`, its constant term is the family's constant term \(C_J\). This combines the previous lemma with the published `range_radical_eq_standardUnipotent`. In Ξ_main, `IsLocalFinitenessGroupData` requires exactly this image for \(u_\alpha\) with \(J=\Delta_0\setminus\{\alpha\}\).
- `StandardParabolicFamily.constantTerm_top`: \(C_G\varphi=\varphi\). The radical of the top index has image `standardUnipotent` of all simple roots, which is trivial (`standardUnipotent_simple_eq_bot`). So every representative in the integral is \(1\), the integrand is the constant \(\varphi(g)\), and the normalized quotient measure is a probability measure. Compactness of the radical quotient is the published `compactSpace_radicalRationalQuotient`.

## Main statements

`isTranslationPolynomialSolution_subgroupConstantTerm` has the hypotheses of `aeval_prod_adelicLeftShift_constantTerm_eq_zero`: `hvan`, a maximal compact \(K\) that is an Iwasawa compact for every member, a closed matrix embedding of positive size, a continuous left-rational \(f\) of moderate growth, one positive point \(a\) of \(A_P\), a finite set \(S\) containing every \(Q\le P\), and polynomials \(D_Q\) with \(D_Q(L_a)\,C_Qf\) in the fibrewise cuspidal annihilator along \(Q\) for every \(Q\le P\). Add a closed subgroup \(u\) with image the standard radical of \(P\) and a point \(x\) equal to the image of \(a\) in \(G(\mathbb A)\). The conclusion is
\[
\texttt{IsTranslationPolynomialSolution}\;x\;\Big(\prod_{Q\in S}D_Q\Big)\;\big(\text{constant term of }f\text{ along }u\big).
\]
The proof substitutes \(x\), applies the two translation lemmas, and quotes the product step.

`isTranslationPolynomialSolution_top` is the case \(P=G\). Here \(S\) contains every standard index, and by `constantTerm_top` the conclusion is the difference equation for \(f\) itself, the form of the central equations of Ξ_main.

`ProductStepLocalFinitenessEquationStatement` states the implication of the first theorem as one proposition: (8.1) implies the constant-term equation for all data as above. `productStepLocalFinitenessEquation` proves it from the first theorem.

## Relation to Bernstein–Lapid

In Ξ_main the shifts are \(a_\alpha=\iota_T(t_\alpha)\) with \(t_\alpha\) in the positive real points of the maximal split torus, and \(z_j\) likewise. The theorems here apply when such a point is the image of a positive point of \(A_{P_\alpha}\) (respectively \(A_G\)); that identification is the hypothesis `hx` and is not proved here. The degree and holomorphy requirements of `LocalFinitenessData.IsAdmissible` on \(\prod_Q D_Q\) are also not addressed. As in `AdelicCuspidalProductVanishing`, every factor uses the same point \(a\), and BL's normalized difference \(\Delta^{P,\lambda}_a\) is the nonzero multiple \(\delta_P(a)^{-1/2}(X-a^{\lambda+\rho_P})\) of a monic polynomial in \(X=L_a\).

## Dependencies

The module imports `AdelicCuspidalProductVanishing` and the published `AdelicLocalFinitenessStatement`.
