# Positivity of actual rational self-isogeny multipliers

`Langlands.AbelianScheme.Rosati.multiplierPositivity` proves the existing
`MultiplierPositivityStatement.{u}` for arbitrary `u`. For a geometrically
polarized abelian scheme over an algebraically closed field of characteristic
zero with `id0 A ≠ 0`, the multiplier `q : ℚˣ` of a rational self-isogeny
satisfying `IsRationalDualPullbackMultiple` is strictly positive in `ℚ`.

The proof applies the published `multiplierPositivity_of_positivity` to the
published `positivity` theorem at the same universe. The reduction obtains the
rational inverse of the polarization from the geometric polarization
hypothesis. With `f = e.hom`, composing the pullback equation with this inverse
gives `f† * f = q • id0 A`, where `f†` is the actual Rosati conjugate. The
rational isomorphism and the nonzero identity imply `f ≠ 0`. Rosati conjugation
fixes the identity, so strict positivity at the identity and at `f` gives
`Tr(id0 A) > 0` and `Tr(f * f†) > 0` for the fixed geometric trace. Cyclicity
and rational linearity identify the latter trace with `q * Tr(id0 A)`, which
forces `0 < (q : ℚ)`.

This is an internal consequence of the two published theorems. The underlying
Rosati positivity result is the characteristic-zero specialization of Milne,
*Abelian Varieties*, January 2, 2022 author revision, Theorem 17.3,
pp. 35–36, as described in the paired statement and positivity proof.
