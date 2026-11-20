# Weil truncation quotients at finite Kummer stages

`Langlands.Ramification.Kummer.kummerStageWeilQuotient` proves
`KummerStageWeilQuotientStatement.{u}` in an arbitrary universe `u`.
For a compatible system of uniformizer roots, let `K_n` be the field
of `kummerStage F πs n` and let `b = kummerBreak F = p e_F/(p - 1)`.

Given `-1 ≤ x ≤ b`, transitivity of the order gives `-1 ≤ b`.
Applying `kummerTowerUpperSup` at `b` gives the supremum of the fixing
subgroup of `K_n` and the absolute upper group of `F` at `b` as the whole
absolute Galois group of `F`. This is the hypothesis of
`truncationWeilQuotient` with transitivity index `b`. Applying that
theorem at `x` gives `WeilTruncationIsoAt F (kummerStage F πs n) x`.
The isomorphism is induced by `intermediateWeilMap`, and it identifies the
images of the upper Weil groups at every index `y` with `-1 ≤ y ≤ x`.
The two imported theorems apply to the endpoints and to stage zero as well.

This implements the finite-stage Weil quotient assertion in the first
sentence of Corollary `cor:kummer` of the operator's *Numerical local
Langlands for GL_n, counts on the two sides and the recommended route*
(`operator-numerical-llc-route-2026-11-16`, lines 876–898). The
[statement documentation](TruncationQuotientStatement.md) explains the
index conventions.
