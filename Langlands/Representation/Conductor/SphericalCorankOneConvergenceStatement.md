# Convergence of the corank-one integrals against the spherical functions

Authors: Worker 8 and Worker 5220. This module defines one proposition,
`Langlands.Conductor.SphericalCorankOneConvergenceStatement` (universes `uF`,
`uV`). It is a statement only: nothing in this module proves it. The theorem
`Langlands.Conductor.sphericalCorankOneConvergence`, in the separate module
[`SphericalCorankOneConvergenceProof`](SphericalCorankOneConvergenceProof.md),
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
Jacquet's `W(g; x; ψ̄)` on `GL_(n+1)(F)`. The conclusion is the first two
conjuncts of `SphericalLFactorGenerationStatement`: there is `P : ℂ[X]` with
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P` (that is,
`L(s, π × 1) = P(q^(-s))⁻¹` with `P(0) = 1`) such that for every vector `w` of
`coefficientModel π ℓ` and every `x : Fin (n + 1) → ℂˣ` there is `a : ℝ` with
`CorankOneConverges ψ abv μ w W_x s` for every `s` with `a < Re s`.

`P` is chosen before `w` and `x`; the bound `a` may depend on `w` and `x`.
The target's second and third conjuncts (the Laurent numerator and the
generation identity) are not part of this statement.

## Source

JPSS 1983 (H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464, literature ID
`jpss-1983-rankin-selberg`), Theorem (2.7): the existence of the standard
L-factor `L(s, π × 1)` and the absolute convergence of the integrals
`Ψ(s, W, W')` on a right half-plane. Jacquet 2012 (*A correction to Conducteur
des représentations du groupe linéaire*, Pacific J. Math. 260 (2012), 515-525,
literature ID `jacquet-2012-conductor-correction`) recalls both facts in
section 1, printed pages 517 and 519, for `W'` in the Whittaker model of
`I(t)`. Here they are stated for the spherical functions `W_x` for every `x`,
without an ordering hypothesis; for norm-ordered `x`, `W_x` lies in the
Whittaker model of `I(x)` by Jacquet's Lemma 2 and the comparison after it
(printed page 518), and `W_x` is symmetric in `x`.
