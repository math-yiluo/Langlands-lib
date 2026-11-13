# Proof: the Moy–Prasad filtration is separated (KP Proposition 13.2.5)

The theorem `Langlands.Geometry.Building.moyPrasadSeparated` proves the published
proposition `MoyPrasadSeparatedStatement.{u}` (module
`Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement`) at an arbitrary universe `u`.

## Statement proved

For every nonarchimedean local field `F`, every group scheme `G` over `F` with
`IsAffineHom G.X.hom`, all supplied `P : ParahoricBuildingData G` and
`Zf : P.CentralizerFiltration` with `P.SatisfiesApartmentAxioms` and
`Zf.SatisfiesFiltrationAxioms`, and every apartment point `x`,
`⨅ r, Zf.moyPrasad x r = ⊥`. That is, `⋂_r P_{x,r} = {1}`: the "separated" of the opening
sentence of Kaletha–Prasad, Proposition 13.2.5.

## Implemented proof

The proof introduces the quantified data and hypotheses and applies one published Library
theorem:

- `Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.iInf_moyPrasad_eq_bot`
  (module `Langlands.Geometry.Building.MoyPrasadProductCoordinates`). From
  `P.SatisfiesApartmentAxioms` and `Zf.IsCommutatorFriendly` it gives
  `⨅ r, Zf.moyPrasad x r = ⊥` for every apartment point `x`.

`Zf.SatisfiesFiltrationAxioms` is by definition (module
`Langlands.Geometry.Building.KPMoyPrasadFiltration`) the conjunction
`Zf.IsCommutatorFriendly ∧ Zf.IsNormalizerStable ∧ Zf.IsCommutatorFiltered ∧
Zf.IsRootCompatible`. The proof passes its first component `hZ.1` to the theorem above. The
other three components are not used.

## Route of the cited theorem

For orientation only; this module adds no argument of its own. According to its Markdown,
`iInf_moyPrasad_eq_bot` chooses a generic cocharacter and complete finite injective orderings
of the indivisible roots of each sign. At every positive depth `r`, it identifies `P_{x,r}` with
the range of the ordered product of the negative root blocks, the image of `Z(F)_r` and the
positive root blocks (`range_orderedMoyPrasadProduct_eq`). The surjectivity of this product
uses commutator-friendliness, as in KP Proposition 7.3.12(4)–(5). The product map is injective,
and each root block and the centralizer filtration are separated. An element of every `P_{x,r}`
therefore has trivial coordinates, so it is the identity
(`iInf_moyPrasad_eq_bot_of_positive_cover`).

## Scope

The building data and the filtration of `Z(F)` are supplied, exactly as in the statement; this
proof constructs neither. No hypothesis is added to the statement and no unproved proposition
is assumed.
