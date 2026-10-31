# Scalar analytic regularity in zero dimension and zero order

These elementary lemmas handle the degenerate cases of the scalar assertion
without elliptic estimates. They preserve the original normed domain.

## Target

The final theorem `Langlands.Analysis.scalarEllipticAnalyticityDegenerate`
proves `ScalarEllipticAnalyticityDegenerateStatement E` for an arbitrary
`E : Type v` with `[NormedAddCommGroup E]` and `[NormedSpace ℝ E]`. That
published proposition is
`(∀ r : ℕ, ScalarEllipticAnalyticityStatement E 0 r) ∧
(∀ d : ℕ, ScalarEllipticAnalyticityStatement E d 0)`.
Each conjunct is the unchanged generic scalar assertion: for every actual
`D : CoordinateScalarOperator E d r`, open `S` and `F : E → ℂ`, analytic
coefficients, ellipticity, smoothness of `F` on `S` and the full
homogeneous equation `∀ x ∈ S, D.action F x = 0` give
`AnalyticOnNhd ℝ F S`. The closing `example` records the theorem's type
with `E` and its instances universally quantified.

## Proof

`scalarEllipticAnalyticity_of_subsingleton` proves the generic assertion
for every `d` and `r` when `E` is a subsingleton. Every point of `E`
equals `0`, so `F` equals the constant function with value `F 0`. A
constant function is analytic near every point (`analyticOnNhd_const`).

`scalarEllipticAnalyticity_dimension_zero` treats dimension zero at every
order `r`. The operator's actual basis `D.basis`, indexed by `Fin 0`,
gives the injective coordinate map `D.basis.equivFun` into functions on
`Fin 0`. That function space is a subsingleton, so `E` is one too, and
the previous lemma applies.

`scalarEllipticAnalyticity_order_zero` treats order zero at every
dimension `d`. Dimension zero is supplied by the previous lemma. In
dimension `d + 1`, composing the continuous coordinate equivalence
`D.basis.equivFunL` with the projection to index `0` gives a real
continuous covector `ξ`. It takes the value `1` on the basis vector
`D.basis 0`, so `ξ ≠ 0`. At order zero there is exactly one derivative
word, the empty one, and its symbol product is empty. So unfolding
`principalSymbol` shows that ellipticity at `ξ` makes the zero-order
coefficient at `x` nonzero. Unfolding `action` turns the full
zero-order equation into the product of that coefficient with `F x`
being zero. Therefore `F x = 0` for every `x ∈ S`. At each point of the
open set `S`, `F` agrees on a neighbourhood with the analytic zero
function, so `F` is analytic there.

This argument uses neither coefficient analyticity nor smoothness of `F`,
although the target keeps both hypotheses. The zero-dimensional case also
does not use openness, ellipticity or the equation.

The final theorem pairs `scalarEllipticAnalyticity_dimension_zero E` and
`scalarEllipticAnalyticity_order_zero E`, which are exactly the two
conjuncts.

## Scope and provenance

This proof module imports only the statement module and Mathlib. It is
independent of the coordinate transport construction and the canonical
Euclidean regularity assertion.

This is an internal elementary proof by Worker 116. Worker 1099 expanded
this documentation. It proves no positive-dimension, positive-order
analytic regularity theorem and does not complete the parent
joint-finite analyticity task.
