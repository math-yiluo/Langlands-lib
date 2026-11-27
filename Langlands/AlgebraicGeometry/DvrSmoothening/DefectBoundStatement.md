# Boundedness of the defect of smoothness

The module `Langlands.AlgebraicGeometry.DvrSmoothening.DefectBoundStatement` contains one
proposition, `DefectBoundStatement`, and proves nothing.

## The proposition

`DefectBoundStatement` quantifies over a universe `u`, a discrete valuation ring `R` with an
irreducible element `ϖ`, and an `R`-algebra `A` of finite type with
`Algebra.Smooth R (Localization.Away (algebraMap R A ϖ))` (smooth generic fibre). It asserts a
natural number `n` such that `pointDefect φ ≤ n` for every discrete valuation ring `R'` in
universe `u` with a local homomorphism `R → R'` satisfying
`Langlands.AlgebraicGeometry.IsRamificationIndexOne R R'`, and every `φ : A →ₐ[R] R'`.

## Source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models` (SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is PDF
page `p + 7`):

- §3.3, Proposition 3, printed pp. 66–67: for an `R`-scheme `X` of finite type with smooth
  generic fibre there is an integer `c` with `δ(a) ≤ c` for all `a ∈ X(R^{sh})`. The proof
  reduces to `X` affine and bounds `δ` through the Jacobian minors and an identity
  `Σ f_i Δ_i = π^c`, which bounds `v(a*Δ_i)` for every point at which the uniformizer `π` keeps
  valuation one.
- §3.6, printed p. 79, extends `δ` to points with values in extensions `R'` of ramification
  index 1, for which `π` is a uniformizer of `R'`; the bound of 3.3/3 holds for them by the
  same argument.

The proposition is the affine case for all points with values in discrete valuation rings of
ramification index one over `R`, which include the local étale extensions of `R` and `R^{sh}`.
