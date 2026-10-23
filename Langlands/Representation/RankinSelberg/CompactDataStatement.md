# Simultaneous compact families of equal-rank data

`Langlands.RankinSelberg.EqualRankCompactDataStatement F n` states that the
simultaneous right translates of two coefficient-model vectors and one
Schwartz–Bruhat row function form a locally constant family on `GL_(n+1)(F)`.
The family has finite range when restricted to any compact subset.

The field has a topology making its ring operations continuous. The two
complex representations are smooth, with independently quantified carrier
universes. Their specified functionals use respectively the standard character
of a unitary additive character and its inverse. The functionals may be zero.
No irreducibility, admissibility, finite generation, or uniqueness of a
functional is assumed. In particular the statement applies to the smooth
representations occurring in the equal-rank analytic problem, including
reducible ones.

The tuple records actual vectors in the coefficient images, acted on by their
inherited representations, and the actual row function `x ↦ Φ(xg)`. Evaluating
the two model vectors at `h` gives `f(hg)` and `f'(hg)`. Equality of tuples
therefore identifies all three translates simultaneously. The row component
is a function on every row, not merely the support of `Φ`. Local constancy
is a property of a map to a set; no topology on a representation carrier or
function space is needed. The compact subset need not be a subgroup.

This is a derived supporting statement motivated by the proof of Theorem 2.7
in Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983),
printed p. 391, paragraph immediately before display (3). There the compact
group finiteness of the two Whittaker functions and the row test is used
together. The generalized formulation here isolates that topological step.
Its proposed derivation combines smoothness of coefficient images, local
constancy of smooth orbit maps, and the open stabilizer of a compactly
supported locally constant row function. A locally constant map on a compact
space has finite range. This module defines the proposition only.

No integration formula, convergence, rational continuation, common denominator,
or normalized generator is asserted.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391.
