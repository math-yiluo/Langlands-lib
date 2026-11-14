# Convergence and Laurent numerators of the corank-one spherical integrals

Author: Worker 8. This module defines one proposition,
`Langlands.Conductor.SphericalCorankOneLaurentStatement` (universes `uF`,
`uV`). It is a statement only: nothing in this module proves it. The theorem
`Langlands.Conductor.sphericalCorankOneLaurent`, in the separate module
[`SphericalCorankOneLaurentProof`](SphericalCorankOneLaurentProof.md),
proves it.

## Statement

The binders are exactly those of the published
`Langlands.Conductor.SphericalLFactorGenerationStatement`
([`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md)),
in the same order: a nonarchimedean local field `F : Type uF` of any
characteristic, `n : ℕ`, the measurable and Borel structures, `q`, `ψ`, `abv`,
`ϖ`, `μ`, `h : IsJacquetNormalization q ψ abv ϖ μ`, `V : Type uV`, a
representation `π` of `GL_(n+2)(F)` on `V` with `IsGeneric ψ (n + 1) π`, and
`ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`.

Write `W_x` for `inverseSphericalWhittaker h.conductor.1 h.uniformizer q x`,
Jacquet's `W(g; x; ψ̄)` on `GL_(n+1)(F)`, `Ψ(s, w, W')` for
`corankOneIntegral ψ abv μ w W' s`, and `X = spectralPoint q s` (`= q^(-s)`).
The conclusion is the first three conjuncts of
`SphericalLFactorGenerationStatement`, in the same form: there is `P : ℂ[X]`
with `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P` (that is,
`L(s, π × 1) = P(q^(-s))⁻¹` with `P(0) = 1`) such that

1. for every vector `w` of `coefficientModel π ℓ` and every
   `x : Fin (n + 1) → ℂˣ` there is `a : ℝ` with
   `CorankOneConverges ψ abv μ w W_x s` for every `s` with `a < Re s`;
2. for every `w` and every `x` there are `a : ℝ`, `N : ℤ` and `Q : ℂ[X]` with
   `Ψ(s, w, W_x) · (∏ i, P.comp (C (x i) * X)).eval (q^(-s)) = q^(-Ns) Q(q^(-s))`
   for every `s` with `a < Re s`. That is,
   `Ψ(s, w, W_x) ∏_i P(x_i q^(-s))` is a Laurent polynomial in `q^(-s)` on a
   right half-plane.

Items 1 and 2 are clauses 1 and 2 of the target's Markdown. `P` is chosen
before `w` and `x`; the bounds `a`, the exponent `N` and the polynomial `Q` may
depend on `w` and `x`. The target's fourth conjunct (clause 3 of its Markdown,
the generation identity, the analogue of Jacquet 2012, Lemma 4, for the JPSS
polynomial `P`) is not part of this statement.
`x` ranges over all of `(ℂˣ)^(n+1)`, with no ordering or unitarity condition.

## Source

JPSS 1983 (H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464, literature ID
`jpss-1983-rankin-selberg`), Theorem (2.7) (printed pages 390-391): the
standard L-factor `L(s, π × 1)`, the absolute convergence of the integrals on
a right half-plane, and the fact that they lie in
`L(s, π × π') ℂ[q^(-s), q^s]`; Theorem (3.1)(ii) (printed pages 404-405): for
`π'` induced from characters `χ_i`, `L(s, π × π')` lies in
`∏_i L(s, π × χ_i) ℂ[q^(-s), q^s]`. Jacquet 2012 (*A correction to Conducteur
des représentations du groupe linéaire*, Pacific J. Math. 260 (2012), 515-525,
literature ID `jacquet-2012-conductor-correction`) recalls these facts in
section 1, printed pages 517-519, for `W'` in the Whittaker model of `I(t)`;
with `x_i = q^(-t_i)`, `L(s + t_i, π) = P(x_i q^(-s))⁻¹`.

Provenance: derived. The proposition is literally the published
`SphericalLFactorGenerationStatement` without its last conjunct. It is stated
separately because the last conjunct needs Jacquet's Lemma 3 (JPSS 1983,
Theorem (9.4)), while the first three follow from Theorems (2.7) and (3.1).
For norm-ordered `x`, `W_x` lies in the Whittaker model of `I(x)` (Jacquet's
Lemma 2 and the comparison after it, printed page 518); `W_x` is symmetric in
`x`, so the clauses for all `x` follow from those for norm-ordered `x`.
