# Canonical unit witnesses for anisotropic diagonal Hermitian forms

This internal adapter derives canonical weight units from the published
`DiagonalForm.IsAnisotropic` predicate and removes a choice from the actual
Hermitian group model used in the local rank-one classification. It does not
assert that a given group has a Hermitian presentation.

For a diagonal Hermitian form over a field `L`, the self-pairing of the coordinate
vector `Pi.single i 1` is its weight at `i`. If that weight were zero,
anisotropy would force the coordinate vector to vanish. Evaluating at `i`
would give `1 = 0`. Thus `weight_ne_zero` proves that every weight is nonzero.
`anisotropicUnits` uses `Units.mk0` on these coefficients; its value is the
original weight. `exists_unitWitnesses` packages the resulting witnesses.
The finite index type may be empty, and its universe is independent of `L`.

`unitWitnesses_eq` works over any commutative ring and any index type: two
families of units with the same underlying weights agree by unit
extensionality. Over a field it identifies every witness family with
`anisotropicUnits`. Consequently `groupScheme_eq_of_unitWitnesses` gives an
equality of the actual equalizer group schemes for any two witness families.
After equality of those families, the remaining witness equations agree by
proof irrelevance.

For a separable quadratic field extension `L/k`, `anisotropicGroupScheme`
applies the published `SchemeModel.groupScheme` to the canonical units.
Both fields lie in an arbitrary common universe; its finite middle index
is in `Type`, as required by that model. The theorem
`groupScheme_eq_anisotropicGroupScheme` identifies any supplied-witness
model with this canonical model. Finally, `exists_model_iso_iff` equates
the existence of an identification with a supplied-witness model and an
identification with the canonical model, for any group scheme `G` over `k`
and any given anisotropic middle form.

The provenance is derived from the published diagonal pairing, its
anisotropy predicate, the actual equalizer group model, and the standard
field-unit construction. The proof uses no classification, local-field
input, or characteristic restriction. The classification still needs to
construct the field extension, anisotropic form, dimension bound, and
group-scheme identification.
