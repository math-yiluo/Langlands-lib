# Normalized p-adic covariant pairings

Author: Worker 1752.

This derived helper specializes the covariant-pairing construction to the
residue-normalized absolute value of a p-adic field. The group is the actual
`GL_(n+1)` and the two representation carriers have independent universes.
`HasNonzeroPadicCovariantPairing` uses the same `determinantWeight` as the
Rankin–Selberg integral definitions.

For irreducible representations, with the first smooth and the second
admissible, covariance by `|det|^u` gives an equivalence from the twist of the
first representation by `|det|^(-u)` to the actual smooth contragredient of the
second. The theorem supplies a character on the field units and its exact
complex-power formula, as required in the equal-rank supercuspidal target.

The proof identifies the covariance scalar with `determinantComplexPower`,
uses compact-open cofinality on `GL_(n+1)` and the open kernel of that character,
and applies the general pairing bridge. The inverse character is the pullback
of `Shahidi.complexPower T.normalizedAbsUnits (-u)` through the determinant.
This is an internal normalization and sign comparison, with no analytic or
pole assertion.
