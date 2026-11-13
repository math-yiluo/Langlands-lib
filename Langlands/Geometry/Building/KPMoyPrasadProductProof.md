# Proof: the Moy–Prasad product decomposition at positive depth (KP Proposition 13.2.5(3))

The theorem `Langlands.Geometry.Building.moyPrasadProduct` proves the published
proposition `MoyPrasadProductStatement.{u}` (module
`Langlands.Geometry.Building.KPMoyPrasadProductStatement`) at an arbitrary universe `u`.

## Statement proved

Take a nonarchimedean local field `F`, a group scheme `G` over `F` with `IsAffineHom G.X.hom`,
and supplied `P : ParahoricBuildingData G` and `Zf : P.CentralizerFiltration` with
`P.SatisfiesApartmentAxioms` and `Zf.SatisfiesFiltrationAxioms`. Fix an apartment point `x`,
a depth `r > 0` and a cocharacter `ν` with `IsGenericCocharacter P.i ν`. Fix injective lists
`aneg` and `apos` whose ranges are exactly `RelativeRoot.indivisiblePositiveRoots P.i (-ν)`
and `RelativeRoot.indivisiblePositiveRoots P.i ν`. Then the map
`Zf.orderedMoyPrasadProduct x r aneg apos` is injective, and its range is the set of
elements of `Zf.moyPrasad x r`. This map is the ordered product of the blocks
`U_{a,x,r} U_{2a,x,r}` for the roots of `aneg`, then `j(Z(F)_r)`, then the blocks for the
roots of `apos`. The statement is the indivisible-root reading of Kaletha–Prasad,
Proposition 13.2.5(3), recorded in the statement's Markdown.

## Implemented proof

The proof introduces all the quantified data and hypotheses. It then proves the two
conjuncts with two published Library theorems, both in the namespace
`Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration`:

1. **Injectivity.** `orderedMoyPrasadProduct_injective` (module
   `Langlands.Geometry.Building.MoyPrasadOrderedEmbedding`) takes `x`, `r`, `ν`, the two
   lists, their injectivity and their range equalities. It gives
   `Function.Injective (Zf.orderedMoyPrasadProduct x r aneg apos)`. It uses neither the
   apartment axioms, the filtration axioms, `0 < r` nor the genericity of `ν`.
2. **Range.** `range_orderedMoyPrasadProduct_eq` (module
   `Langlands.Geometry.Building.MoyPrasadProductCoordinates`) takes
   `P.SatisfiesApartmentAxioms`, `Zf.IsCommutatorFriendly`, `x`, `r`, `0 < r`, `ν`, its
   genericity and the two range equalities. It gives
   `Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) = (Zf.moyPrasad x r : Set _)`.

`Zf.SatisfiesFiltrationAxioms` is by definition (module
`Langlands.Geometry.Building.KPMoyPrasadFiltration`) the conjunction
`Zf.IsCommutatorFriendly ∧ Zf.IsNormalizerStable ∧ Zf.IsCommutatorFiltered ∧
Zf.IsRootCompatible`. The proof passes its first component `hZ.1` to the range theorem.
The other three components are not used.

## Route of the cited theorems

For orientation only; this module adds no argument of its own. The summary follows the
Markdown of the two cited modules.

- Injectivity: both factors of each block lie in the actual root group `U_a(F)`. The
  published ordered multiplication of the indivisible root subgroups is injective for every
  complete injective ordering of one sign. Each ordered product lies in the dynamic unipotent
  subgroup of its sign. The opposite-cell uniqueness theorem
  `unipotentTripleProduct_injective_of_maps` then separates the negative, central and
  positive factors. The centralizer inclusion `j` is a monomorphism, so the central
  coordinate is determined as well.
- Range: `Zf.moyPrasad x r` is first rewritten, for `r > 0` and a generic `ν`, as the product of
  the negative root span, `j(Z(F)_r)` and the positive root span
  (`moyPrasad_eq_negative_image_positive`, module
  `Langlands.Geometry.Building.MoyPrasadGlobalExchange`). This step uses the apartment
  axioms and commutator friendliness. Each sign span is the
  range of the ordered block product for a complete list of that sign
  (`range_orderedPositiveFiltrationBlockProduct_eq_iSup`, module
  `Langlands.Geometry.Building.MoyPrasadPositiveCollection`).

## Scope

The building data and the filtration of `Z(F)` are supplied, exactly as in the statement; this
proof constructs neither. No hypothesis is added to the statement and no unproved proposition
is assumed. The axioms reported for the theorem are `propext`, `Classical.choice` and
`Quot.sound`.
