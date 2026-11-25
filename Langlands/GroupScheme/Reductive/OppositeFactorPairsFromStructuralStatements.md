# Opposite factor pairs from supplied rank-one cells and root lines

Module `Langlands.GroupScheme.Reductive.OppositeFactorPairsFromStructuralStatements`.

## Purpose

`AlgClosedOppositeFactorPairsStatement.{u}` (module
`Rational.AlgClosedOppositeFactorPairsStatement`) is the rank-one input of the opposite-pair
big-cell assembly `steinbergBigCellIndependent` (module
`Reductive.SteinbergBigCellIndependentProof`), which proves the Steinberg big-cell data
independently of the excluded dynamic-Borel inputs. This module derives it from three
existing Library statements. All three are explicit hypotheses and are not proved here:

- `RootDatumExistenceStatement.{u}` (`Reductive.RootDatumStatement`): every split maximal
  torus of a connected reductive group over a field has a finite reduced root datum.
  Its independent proof is `rootDatumExistenceIndependent` (module
  `Reductive.RootDatumExistenceIndependent`).
- `SplitRankOneRootCellStatement.{u}` (`Reductive.SplitRankOneRootCellStatement`): in
  semisimple rank one, with a supplied root datum, there are additive maps `xp, xm` with
  torus weights `±α`, an open triple cell `xm · T · xp`, and the rank-one relation.
  Its independent proof is `splitRankOneRootCellIndependent` (module
  `Reductive.SplitRankOneRootCellIndependentProof`).
- `SplitRootLieLineStatement.{u}` (`Reductive.SplitRootLieLineStatement`): root spaces of
  the Lie algebra are lines. Its independent proof is `splitRootLieLine_independent` (module
  `Reductive.SplitRootLieLineIndependentProof`).

## Results

1. `exists_oppositeFactorPair_of_rankOne_of_structuralStatements hcell hline hG hT i hi P hP
   hrank r x hx hx1`. Take a connected reductive `G` over any field `k : Type u`, a split
   maximal torus `i`, and a reduced root datum `P` with index type `J : Type u`. Assume any
   two roots are `ℤ`-dependent (`hrank`). Then every rational point `x ≠ 1` of the actual
   root group `RelativeRoot.subgroup i (P.root r)` has an opposite factor pair
   (`RelativeRoot.IsOppositeFactorPair`).
2. `hasOppositeFactorPairs_of_rootDatum_of_structuralStatements hcell hline hG hT i hi P hP`:
   for any connected reductive `G` over any field, split maximal torus `i` and reduced root
   datum `P` with `J : Type u`, `RelativeRoot.HasOppositeFactorPairs i`.
3. `toriAreSplit_of_isSepClosed k`: over a separably closed field every torus is split
   (`ToriAreSplit k`).
4. `algClosedOppositeFactorPairs_of_structuralStatements hRD hcell hline :
   AlgClosedOppositeFactorPairsStatement.{u}`.
5. The definition `RelativeRoot.oppositeFactorPairOfStructuralStatements hRD hcell hline hG
   hi ha x hx hx1 : rationalPoints G × rationalPoints G`, over an algebraically closed
   field, is a chosen opposite factor pair of a nonidentity actual root point.
   `oppositeFactorPairOfStructuralStatements_spec` states that it is one.

## Proofs

(1) and (2) follow the Library proofs `exists_oppositeFactorPair_of_rankOne` and
`hasOppositeFactorPairs_of_rootDatum` (module `Reductive.SplitPinnedOppositeFactorPairs`).
Only the rank-one cell input changes. The Library proof obtains its cell from
`rankOne_exists_rootCell`, which takes `RankOnePositiveRootUniquenessStatement` and
`splitRootLieLine` as inputs, both excluded from the independent big-cell route. Here:

- the additive maps `xp, xm`, their torus weights and the open triple cell come from
  `hcell`;
- the coroot centralizer is the torus: `rankOne_centralizer_isRepresentedBy` with the
  published `dynamicCentralizerReductive`, using `⟨α, α^∨⟩ = 2 ≠ 0`;
- the root datum gives a normalizing point inducing the reflection
  (`IsRootDatumOf.exists_normalizing_latticeReflectionIso`). Its square lies in the torus
  (`RankOneRootCellRelation.exists_sq_eq_of_isNormalizingPoint`). These data form a
  `RankOneRootCellRelation.WeylData`;
- `xp` is a monomorphism, since it is a factor of the open triple cell
  (`Dynamic.mono_right_of_tripleCell`). It is torus-equivariant
  (`VectorGroup.isTorusEquivariant_of_weightPointAction`). By
  `VectorGroup.IsTorusEquivariant.represents_root_of_lie_line` it represents the whole
  actual root group. That lemma needs the root line from `hline` and the absence of
  higher root multiples from reducedness (`RelativeRoot.hasNoHigherRoots_of_isRootDatumOf`);
- so `x = xp(v)` with a nonzero, hence unit, coordinate `v`.
  `WeylData.exists_oppositeFactorPair` gives the pair.

For (2), a cocharacter `ζ` orthogonal to the root and generic for the other roots
(`RootReducedness.exists_cocharacter_pairing_eq_zero`, a lattice lemma) cuts out the
dynamic centralizer `M`. `M` is connected reductive (`dynamicCentralizerReductive`), the
torus stays maximal in it, its roots are pairwise dependent, and the orthogonal root pairing
`orthogonalRootPairing P ζ` is a reduced root datum of it (instance
`orthogonalRootPairing_isReduced`). (1) applies in `M`, and the pair maps back to `G`
(`LeviGluing.root_map_centralizer`, `IsOppositeFactorPair.map`).

(3) applies `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` with the published
`separablyClosedGroupLikeSpanning`. (4) turns the maximal split torus into a maximal torus
using (3) (`IsMaximalSplitTorus.isMaximalTorus`), takes a reduced root datum from `hRD` and
applies (2). (5) is `Classical.choose` of (4).

## Independence

A closure audit over project constants found that all six declarations reach none of the
excluded inputs. It also covered the new inputs
`rankOne_centralizer_isRepresentedBy`, `RelativeRoot.hasNoHigherRoots_of_isRootDatumOf`,
`orthogonalRootPairing_isReduced`, `Dynamic.mono_right_of_tripleCell` and
`VectorGroup.isTorusEquivariant_of_weightPointAction`. The excluded inputs are:

- `ParabolicDynamic*`, `RegularCocharacterBorel*`, `RankOneSolvableObstruction*`,
  `RankOneBorelDynamic*`, `RankOnePositiveRootUniqueness*`;
- `rootDatumExistence`, `rootReducedness`, `reductiveGeometricReductivity`,
  `absoluteBruhatCovering`, `steinbergBigCell`;
- `splitRootLieLine`, `splitRankOneRootCell`, `isParabolicSubgroup_of_range_eq_dynamicParabolic`;
- the projective-Borel helpers.

An earlier audit covered the remaining inputs shared with the Library proof:
`dynamicCentralizerReductive`, `dynamicCentralizerRoots`, the `RootReducedness` lattice
lemmas, `orthogonalRootPairing`, `root_map_centralizer`,
`exists_normalizing_latticeReflectionIso`, `exists_sq_eq_of_isNormalizingPoint`,
`WeylData.exists_oppositeFactorPair`, `represents_root_of_lie_line` and `field_base`.
As controls, the Library's `rankOne_exists_rootCell` and `hasOppositeFactorPairs_of_rootDatum`
are flagged.

## Provenance

This is an internal reassembly of Library constructions. The structural statements are
supplied as hypotheses. Mathematically, the result is the existence part of
Kaletha–Prasad Proposition 2.11.17 (Conrad–Gabber–Prasad Proposition C.2.24(i)) for split
reductive groups, proved by reduction to rank one and the `SL₂` Weyl element of the root
cell.

The shared `toriAreSplit_of_isSepClosed` declaration and its unchanged coalgebra proof are in [`Torus.SeparablyClosedSplitting`](../Torus/SeparablyClosedSplitting.md). The structural assembly imports that single declaration.
