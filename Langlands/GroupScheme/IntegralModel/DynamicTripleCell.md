# Integral three-factor cells from actual dynamic representatives

Author: Worker 209.

This is derived infrastructure for the integral open-cell step in the proof of
Kaletha–Prasad Theorem 8.2.9, printed pp. 293–295 / PDF pp. 324–326
(`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).
The proof uses only published Library theorems. It extends the existing
field-base construction in `Langlands.GroupScheme.Absolute.TripleCell` using
the published arbitrary-base opposite-cell and representability theorems.

## The ordered cell over any base

For a smooth affine group scheme `G` over any scheme `S`, and a cocharacter
`χ : Gm → G`, the theorem
`Dynamic.isOpenImmersion_tripleCellMultiplication_overBase`, imported from
[Dynamic/BaseTripleCell](../Dynamic/BaseTripleCell.md), proves that the
actual multiplication

`U(-χ) ×_S (Z(χ) ×_S U(χ)) → G`

is an open immersion. Here `-χ` means precomposition with inversion on `Gm`.
The sources and their maps into `G` may be any actual representatives of the
specified intrinsic dynamic subgroup functors. The multiplication and its
formula on all test schemes are the existing
`Dynamic.tripleCellMultiplication` and `Dynamic.lift_tripleCellMultiplication`.

The proof obtains a representative `P` of `P(χ)` from
`dynamicBaseRepresentability`. Smoothness of `G` supplies its local finite
presentation hypothesis. The scheme isomorphism `parabolicProductIso`
identifies `Z(χ) × U(χ)` with `P`; affineness of `G` supplies the separatedness
used by this isomorphism. Precomposing the published open immersion
`dynamicBaseOppositeCell : U(-χ) × P(χ) → G` with this isomorphism gives an open
immersion. The existing
`whiskerLeft_parabolicProductIso_comp_cellMultiplication` identifies the
composite with the original ordered three-factor multiplication.

The base need not be affine, Noetherian, reduced, local, or a field. No
connectedness, reductivity, or splitting assumption on `G` is used.

## Construction of integral cell data

`IntegralModel.IntegralTripleCellData.ofDynamic` takes an integral model `M`
with smooth structure morphism, an integral cocharacter, and three supplied
integral models with compatible maps into `M`. The maps themselves must
represent the negative unipotent, centralizer, and positive unipotent functors
of that cocharacter over the integral base.

The constructor retains those models, maps, and their specified generic-fibre
compatibilities. It fills the `openCell` field of the existing
`IntegralTripleCellData` structure with the theorem above. Thus its existing
ordered congruence-product equivalence applies to these same models and maps.
It does not choose new generic identifications or replace the integral-point
maps.

In KP Theorem 8.2.9 the required cell is formed in a rank-one centralizer
model; the source cites Proposition 2.11.3 for its openness. This module
supplies that geometric step whenever the three integral dynamic models and
maps have been identified. Constructing the rank-one model, identifying its
dynamic subgroups with the desired root groups, lifting a Weyl element, and
establishing residue-cell membership remain separate obligations. This module
does not prove the opposite-factor criterion or the depth-zero target.
