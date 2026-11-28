# Binary norm equations with unit coefficients at a finite completion

Module: `Langlands.Algebra.CentralSimple.LandherrHensel`.

`exists_sq_sub_mul_sq_of_units`: let `K` be a number field, `P` a finite place and `K_P` the
completion. If `a, b ∈ K_P` and `2` all have multiplicative valuation `1`, then `x² - a y² = b` has a
solution in `K_P`.

## Proof

The ring of integers `O_P` of `K_P` is Henselian (`Global.adicCompletionIntegers_henselian`),
`a`, `b`, `2` are units of `O_P`, and its residue field `k` is finite of odd characteristic.
Write `ā` and `b̄` for the residues of `a` and `b`. The lemma
`FiniteField.exists_root_sum_quadratic` gives `x₀, y₀` with `f(x₀) + g(y₀) = 0` for two
univariate polynomials of degree two over a finite field of odd order. Apply it to
`f(X) = X² - b̄` and `g(X) = -ā X²` to obtain `x₀² - ā y₀² = b̄` in `k`.
Lift `x₀, y₀` to `x₁, y₁ ∈ O_P`. If `x₀ ≠ 0`, the monic polynomial
`X² - (b + a y₁²)` has the root `x₀` modulo the maximal ideal with unit derivative `2x₁`, so
Hensel's lemma gives `x` with `x² - a y₁² = b`. If `x₀ = 0`, then `y₀ ≠ 0` since `b̄ ≠ 0`,
and the same argument applies to `X² - a⁻¹(x₁² - b)` at `y₁`.

## Provenance

For nonsquare `a` this is the classical fact that a unit is a norm from an unramified
quadratic extension of a non-dyadic local field. The same residue-field calculation
also covers square `a`. In the proof of Landherr's theorem this argument applies where
`2`, `a` and `b` are local units.
