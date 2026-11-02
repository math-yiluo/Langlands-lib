# Finiteness from close approximations of the coordinates

Author: Worker 1010.

This file proves a finiteness criterion for bounded maps of presented strict
affinoid algebras. It also proves four general lemmas that the criterion uses.

## General lemmas

- `surjective_of_approx_preimage`. Let V be a complete normed additive group,
  W a normed additive group, and Φ : V → W a continuous additive map. Suppose
  there is C ≥ 0 such that every w in W has some v in V with ‖v‖ ≤ C‖w‖ and
  ‖w − Φ v‖ ≤ ‖w‖/2. Then Φ is surjective. Proof: repeat the approximation on
  the remainders. The n-th remainder has norm at most 2⁻ⁿ‖w‖, so the corrections
  form an absolutely summable series in V. Its sum maps to w by continuity.
- `norm_prod_le_pow`. In a normed commutative ring with ‖1‖ ≤ 1, a product of
  factors of norm at most D ≥ 0 over a finset s has norm at most D^|s|.
- `norm_prod_sub_prod_le`. In an ultrametric normed commutative ring with
  ‖1‖ ≤ 1, take two families of factors over s, all of norm at most D ≥ 1, with
  ‖x_k − y_k‖ ≤ η for each k. Then ‖∏ x_k − ∏ y_k‖ ≤ η D^|s|. Proof: induction
  on s, writing x a X − y a Y as x a (X − Y) + (x a − y a) Y.
- `add_pow_eq_sum_range_add_sum_Ico`. The binomial expansion of (x + y)^n,
  split into the terms whose exponent j of x is below N and the terms with
  N ≤ j ≤ n + N. The binomial coefficients act as scalars from a commutative
  semiring K. Terms with j > n vanish.

## Small powers

`PresentedStrictAffinoidAlgebra.exists_norm_pow_le_of_spectrum_lt_one`. Let K be
complete, ultrametric and nontrivially valued, so some c in K has ‖c‖ > 1. Let P
be a presented strict affinoid K-algebra and b an element of P with y(b) < 1 at
every point y of M(P). Then for every η > 0 there is N₀ such that ‖bⁿ‖ ≤ η for
all n ≥ N₀.

Proof. M(P) is compact and evaluation at b is continuous. So some r < 1 bounds
y(b) for all y; if M(P) is empty, take r = 0. Choose n with rⁿ < ‖c‖⁻¹. Then
c bⁿ has spectral values at most 1. The published spectral power bound
(`hasBoundedPowers_of_spectrum_le_one`) gives a uniform bound C₁ for its
powers, and a bound C₂ for the powers of b. Hence ‖b^{nj}‖ ≤ ‖c‖^{−j} C₁. A
general power b^N splits as b^{n⌊N/n⌋} b^{N mod n}. This gives
‖b^N‖ ≤ ‖c‖^{−⌊N/n⌋} C₁ C₂, which is at most η for N large.

## The finiteness criterion

`PresentedStrictAffinoidAlgebra.finite_of_spectrum_coordinate_sub_lt_one`. Let K
be complete, ultrametric and nontrivially valued, and let i : A → B be a bounded
K-algebra map of presented strict affinoid algebras. Write t_k for the
coordinates of B. Suppose there are a_k in A with x(a_k) ≤ 1 at every point x
of M(A), and with y(t_k − i(a_k)) < 1 at every point y of M(B). Then i is
finite (`i.toAlgHom.toRingHom.Finite`).

Proof. Put c_k = t_k − i(a_k), so t_k = c_k + i(a_k).

1. Bounds. The spectral power bound gives uniform bounds for the powers of a_k
   in A and of c_k in B. Together with the bound of i, this gives a uniform
   bound Ci·Ca for the powers of i(a_k). Let D = Cc·Ci·Ca ≥ 1, and choose η > 0
   with η·Ci·Ca·D^m = 1/4, where m is the arity of B. By the small-powers
   lemma there is N with ‖c_k^p‖ ≤ η for all k and all p ≥ N.
2. One-variable approximations. Let P_k(n) be the part of the binomial
   expansion of t_kⁿ = (c_k + i(a_k))ⁿ whose powers of c_k are below N. The
   ultrametric inequality and ‖binomial coefficient‖ ≤ 1 give ‖P_k(n)‖ ≤ D,
   ‖t_kⁿ − P_k(n)‖ ≤ η·Ci·Ca, and hence ‖t_kⁿ‖ ≤ D.
3. Monomials. For a multi-index d, multiplying out ∏_k P_k(d_k) writes it as
   Σ_β i(coef(d, β))·c^β. Here β ranges over the functions from coordinates
   to exponents below N, c^β = ∏_k c_k^{β_k}, and every coef(d, β) in A has
   norm at most Ca^m. The product lemma gives
   ‖t^d − Σ_β i(coef(d, β))·c^β‖ ≤ η·Ci·Ca·D^m = 1/4.
4. Approximate preimages. Let Φ : A^{N^m} → B be the coefficient map of i on
   the finitely many monomials c^β (`BoundedAlgHom.coefficientMap`). Take b in
   B with b ≠ 0. Choose a Tate series F representing b with ‖F‖ < 2‖b‖
   (`exists_representative_norm_lt`), and a finite truncation of F within
   ‖b‖/2 of F (`hasSum_monomials`). Replacing each monomial t^d of the
   truncation by its approximation from step 3 gives coefficients G in A with
   ‖G‖ ≤ 2·Ca^m·‖b‖ and ‖b − Φ G‖ ≤ ‖b‖/2. The error has two parts: the
   truncation error, bounded through the quotient norm, and the monomial
   errors, each bounded by ‖F‖/4.
5. `surjective_of_approx_preimage` makes Φ surjective. The published
   criterion `BoundedAlgHom.finite_iff_exists_surjective_coefficientMap` then
   gives finiteness.

## Scope and provenance

This is an internal supporting result for the strict local
rational-neighbourhood theorem (`StrictTestDomain.LocalRationalNeighborhoodStatement`).
There it shows that the comparison map to a represented domain is finite on a
small rational neighbourhood. In Temkin's proof of the Gerritzen–Grauert theorem
(Math. Ann. 2005), this step uses reduction theory and the finiteness criterion
of Bosch–Güntzer–Remmert (6.3.5). The criterion here is a different statement,
proved directly by approximation and iteration, with no reductions and no
Weierstrass theory. It cites no specific numbered external result. The
hypotheses are pointwise spectral inequalities, and no Noetherian or
reducedness hypothesis is used.
