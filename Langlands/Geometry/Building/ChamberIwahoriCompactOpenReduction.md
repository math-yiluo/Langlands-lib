# Reduction of chamber Iwahori compact openness

Lean module: `Langlands/Geometry/Building/ChamberIwahoriCompactOpenReduction.lean`.

This module reduces the published target
`ParahoricBuildingData.ChamberIwahoriCompactOpenStatement` to three prerequisites:
the published statements `RelativeRoot.OpenRootCentralizerGenerationStatement` (KP
Corollary 8.2.6) and `ParahoricBuildingData.ChamberIwahoriDecompositionStatement`,
and compactness and openness of `Z(F)^0` in `Z(F)`, taken as two plain `IsCompact`
and `IsOpen` premises. It proves no prerequisite. Each one stays an explicit premise
of the theorems below.

## Setting

Throughout, `F` is a nonarchimedean local field at arbitrary universe `u`, `G` is
a group scheme over `F` with its affine structure morphism, and
`P : ParahoricBuildingData G` is actual building data. `G(F)` carries
`rationalPointTopology F G.X`. `Z(F)` carries `rationalPointTopology F Z.X`, for the
actual centralizer `Z = Z_G(S)` of `P`, with the affine instance coming from the
closed immersion `j : Z → G`. These are the same instances used by
`KPParahoricProductTopology` and by the published centralizer-zero statement.

## Openness

- `isOpen_parahoricAt_of_openRootGeneration`: assume V 7
  (`P.apartment.IsTopologyCompatible`), KP Corollary 8.2.6
  (`RelativeRoot.OpenRootCentralizerGenerationStatement.{u}`), and openness of
  `Z(F)^0` in `Z(F)`. Then the point parahoric `P_x` is open in `G(F)` for every
  apartment point `x`.

  Proof: by definition `P_x = j(Z(F)^0) ⊔ ⨆_a U_{a,{x},0}`, the supremum over the
  actual relative roots `a`. Instantiate Corollary 8.2.6 at `G`, at the actual
  maximal split torus `S` and at the actual centralizer `j`, with `V a = U_{a,{x},0}`
  and `Z' = Z(F)^0`. Each `U_{a,{x},0}` lies in `U_a(F)` by definition.
  `rootFixer_singleton` identifies it with the filtration `U_{a,x,0}`, which is open
  in `U_a(F)` by V 7 (`filtrationOpenSubgroup`).
- `exists_mem_of_isChamber`: a chamber contains the point that defines it.
- `isOpen_chamberIwahori_of_openRootGeneration`: under
  `SatisfiesApartmentAxioms`, the same premises make `P_C` open for every chamber
  `C`. `chamberIwahori_eq_parahoricAt` identifies `P_C` with `P_x` for a point
  `x ∈ C`.
- `chamberIwahoriOpenSubgroup` (definition) bundles `P_C` as an `OpenSubgroup` of
  `G(F)` under these premises. `coe_chamberIwahoriOpenSubgroup` says its carrier is
  `P_C`.

## Compactness

- `exists_indivisiblePositiveRoots_enumeration`: for every cocharacter `ν`, the set
  of indivisible roots positive on `ν` has an injective enumeration
  `Fin n → relativeRoots P.i`. Finiteness comes from `IsSplitTorus.finite_relativeRoots`.
- `isCompact_chamberIwahori_of_decomposition`: assume `SatisfiesApartmentAxioms`, the
  chamber decomposition target `P.ChamberIwahoriDecompositionStatement` (KP 7.4.9
  with its full-parahoric consequences), and compactness of `Z(F)^0`. Then `P_C` is
  compact for every chamber `C`.

  Proof: pick `x ∈ C` and a generic cocharacter `ν`
  (`IsSplitTorus.exists_genericCocharacter`). Enumerate the indivisible roots
  positive on `-ν` and on `ν`. The last clause of `ChamberIwahoriConclusion` gives
  `P_C` as the range of `orderedIwahoriChamberProduct x false aneg apos`, and
  `isCompact_range_orderedIwahoriChamberProduct` (V 7 plus compact `Z(F)^0`) shows
  that this range is compact.

## Assembly

- `chamberIwahoriCompactOpenStatement_of_prerequisites`: KP Corollary 8.2.6, the
  chamber decomposition target for `P`, and compactness and openness of `Z(F)^0`
  together imply `P.ChamberIwahoriCompactOpenStatement`.

## Provenance

The module is derived. It contains internal consequences of published Library
constructions and statements, namely KP Corollary 8.2.6 (printed p. 291),
Definition 7.4.1 and 7.4.9 as formalized in the Library, and V 7. It adds no new
source assertion. The published target remains unproved until the three
prerequisite statements are proved.
