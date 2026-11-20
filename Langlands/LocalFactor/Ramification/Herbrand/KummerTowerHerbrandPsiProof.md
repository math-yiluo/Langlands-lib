# The inverse Herbrand function of a finite Kummer stage

`Langlands.Ramification.Kummer.kummerTowerHerbrandPsi` proves the published
`KummerTowerHerbrandPsiStatement.{u}` for arbitrary `u`. For a compatible
root system `πs` over a p-adic field `F`, put `K_n = kummerStage F πs n`
and `b = kummerBreak F = p e_F / (p - 1)`, where `e_F` is the absolute
ramification index of `F`.

Given `-1 ≤ x ≤ b`, transitivity of `≤` gives `-1 ≤ b`. The proof applies
`kummerTowerUpperSup` at `v = b` using that inequality and `b ≤ b`. This
gives `G_{K_n} ⊔ G_F^b = ⊤`, where `G_{K_n}` is the fixing subgroup of
`K_n` and `G_F^b` is the absolute upper ramification group of `F` at `b`.
Applying `herbrandPsiTruncation` to `K_n` at threshold `b` yields
`relativeHerbrandPsi K_n x = x` using the two bounds on `x`. Both endpoint
values and stage zero are included.

This combines the finite-stage transitivity argument in Corollary `cor:kummer`
with the inverse Herbrand conclusion of Lemma `lem:trunc` in the operator's
*Numerical local Langlands for GL_n, counts on the two sides and the recommended
route* (`operator-numerical-llc-route-2026-11-16`, lines 876–897). The imported
theorems express both steps in the Library's absolute Galois group conventions.
