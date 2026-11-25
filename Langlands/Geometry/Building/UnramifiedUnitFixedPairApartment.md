# Centralizing pair apartments from unit-fixed neutral models

This internal construction combines the actual split-source closure,
containing-torus lift, coefficient residue comparison, and centralizing
apartment construction. It works over any nonarchimedean local field `F`
in arbitrary universe `u`, with no characteristic restriction.

`UnitFixedContainingTorusData.unramifiedResidueIsMaximalSplit` starts with a
supplied containing-torus record in a smooth integral model over the
original integers. It applies
`IntegralModel.isMaximalSplitTorus_residue_baseChange` to the actual
integral inclusion. Its original residue map is maximal by the record's
`residueMaximal` field, and its extension to the maximal-unramified
integers is split by `unramifiedIsSplit`. The conclusion concerns the
literal residue map of `unramifiedInclusion`. The integer coefficient map
is local by `Valuation.HasExtension.instIsLocalHomValuationInteger`.

`unitFixedPairApartmentOfNeutralModel` takes actual lower
`RelativeComponentModelData N`, and retains the exact equality of the
integral points of `N.full.baseChangeUnramified` with the character-kernel
fixer of the two endpoints. It assumes a connected reductive generic group,
a closed split source torus `S`, and a homomorphism from `S` into the
original apartment torus whose composite is the prescribed inclusion of
`S`. The apartment torus is maximal split after the unramified extension,
and its supplied apartment and centralizer datum satisfy the stated
compatibility. Both endpoints are fixed by the unramified units of `S`.

The construction forms the split integral source in `N.neutral` using
`unitFixedNeutralTorusData`; the full-model equality supplies that theorem's
containment hypothesis. Neutral-model smoothness allows
`unitFixedContainingTorusData` to extend this source to a relative torus
with maximal original residue inclusion. Its `sourceHom` and
`source_comm` retain containment of the original source over `F`.
Its maximal-unramified pullback is split and has the exact generic
identification and equation furnished by `unramifiedGenericIso` and
`unramifiedGeneric_comm`. The preceding residue comparison supplies its
actual residue maximal splitness.

`centralizingPairApartmentOfNeutralTorus` then constructs a rational point
`g` centralizing `S` after unramified extension. Every coefficient-Galois
difference `g⁻¹ σ(g)` normalizes the original apartment torus after that
extension. The result includes actual apartment coordinates of both
endpoints in the chart translated by this same `g`.

The provenance is composition of these named internal Library
constructions. No descended containing torus or integral lift is retained
as an additional input. Construction of the lower pair model and its
exact full-model equality remains outside this conditional module; in
particular, this module alone does not prove
`UnramifiedFixedPairSpecialApartmentStatement`, the statement it serves.
