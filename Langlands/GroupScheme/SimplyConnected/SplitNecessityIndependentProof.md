# Simple connectedness forces integral coroot generation, via rank-one central covers

`Langlands.GroupScheme.splitSimplyConnectedCorootSpanIndependent` proves the
published proposition
`Langlands.GroupScheme.SplitSimplyConnectedCorootSpanStatement.{u}` for every
universe `u`, with that proposition unchanged as its type.
[Published statement](SplitNecessityStatement.md)

The statement has the following scope. Let `k : Type u` be an arbitrary field
and let `G` be algebraically simply connected over `Spec k` in the Library's
sense: `G` is semisimple, and every incoming central isogeny from a semisimple
group is an isomorphism. Let `i : T.toGrp ⟶ G` be a maximal torus with `T`
split, and let `P` be a root datum of `i` on the actual integral character and
cocharacter lattices of `T`, with `IsRootDatumOf i P`, a finite root index
type `J : Type u` and `P.IsReduced`. The theorem gives `P.corootSpan ℤ = ⊤`:
the integral coroots generate the full cocharacter lattice. The proof adds no
hypothesis to the proposition. There is no restriction on the characteristic
and no algebraic-closure assumption, and no rank-one cell, Lie-line,
classification or root-existence premise.

## Implemented proof

The theorem is one application:

```lean
splitSimplyConnectedCorootSpan_of_corootSpanLineInputs
  ⟨rootDatumExistenceIndependent, splitRankOneRootCellIndependent,
    splitRootLieLine_independent⟩
```

`splitSimplyConnectedCorootSpan_of_corootSpanLineInputs` is the
published conditional reduction. It derives the target from the bundle
`SplitCorootSpanLineInputs.{u}`, the conjunction of `RootDatumExistenceStatement.{u}`,
`SplitRankOneRootCellStatement.{u}` and `SplitRootLieLineStatement.{u}`.
[Conditional reduction](SplitCorootSpanLineReduction.md)
The three components of the bundle are discharged by three proofs of these
unchanged published propositions:

1. `rootDatumExistenceIndependent : RootDatumExistenceStatement.{u}`
   composes `rankOneCentralCover`,
   `rankOneRootReducedness_of_centralCover` and
   `rootDatumExistence_of_rankOneReducedness`.
   [Root-datum existence](../Reductive/RootDatumExistenceIndependent.md)
2. `splitRankOneRootCellIndependent : SplitRankOneRootCellStatement.{u}`
   is `splitRankOneRootCell_of_centralCover rankOneCentralCover`.
   [Rank-one root cell](../Reductive/SplitRankOneRootCellIndependentProof.md)
3. `splitRootLieLine_independent : SplitRootLieLineStatement.{u}`
   is `splitRootLieLine_of_centralCover rankOneCentralCover`.
   [Root Lie lines](../Reductive/SplitRootLieLineIndependentProof.md)

All three use the same published theorem `rankOneCentralCover`. Over an
algebraically closed field it gives the central isogeny from `SL₂ × C` in the
nonempty rank-one case. It is obtained from the ordinary Borel quotient `G/B`.
Białynicki-Birula limits, the classification of torus-fixed points and Hartogs
extension bound `dim G/B` by one. The general curve lemmas
`HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` and
`HomogeneousQuotient.unipotent_dimension_le_one` then apply to this bound and
to the noncontainment of the dynamic unipotent subgroup in `B`.
[Central cover](../Reductive/RankOneCentralCoverProof.md)

The reduction itself proceeds as follows, with the details in its Markdown.

- The root cell and the root Lie lines give the Isomorphism Theorem for a
  common split maximal torus (`splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine`,
  Milne Theorem 23.25 with Remark 23.26). The rank-one case comes from the
  root cell (`splitRankOneCommonTorusIsomorphism_of_rootCell`). The gluing
  step comes from the graph-projection isomorphisms over an algebraic
  closure, with one-dimensional root spaces of the graph group taken from
  the Lie-line input (`LeviGluing.algClosedGraphProjectionIsomorphisms_of_rootLieLine`),
  and then descent (`LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs`).
- With root-datum existence, `splitCentralTorusQuotient` and
  `centralIsogenyRootDatumHom`, that theorem gives the existence half of the
  central Isogeny Theorem (`splitCentralIsogenyExistence_of_corootSpanLineInputs`,
  through `splitCentralIsogenyExistence_of_commonTorusIsomorphism`; Milne
  Theorem 23.9).
- The Library assembly `splitSimplyConnectedCorootSpan_of_inputs` combines
  this with the published Existence Theorem `splitReductiveExistence` and the
  semisimplicity criterion `splitSemisimpleRootDatum`. Since `G` is
  semisimple, the coroots of `P` span a sublattice of finite index. The split
  group with the simply connected root datum of `P` on that coroot lattice
  maps to `G` by a central isogeny that realizes the inclusion of root data.
  Simple connectedness makes this isogeny and its torus map isomorphisms, so
  the coroot span is the whole cocharacter lattice.

## Independence

The following are excluded: `ParabolicDynamicStatement`,
`RegularCocharacterBorelStatement`, `RankOneSolvableObstructionStatement`,
`RankOneBorelDynamicStatement` and `RankOnePositiveRootUniquenessStatement`;
their proofs; the regular-cocharacter/Borel route and results downstream of
it; the old proofs `rootDatumExistence`, `rootReducedness`,
`splitRankOneRootCell`, `splitRootLieLine` and
`rootLieLine_of_dynamicCentralizerReductive`; the projective-Borel tangent
chain; `reductiveGeometricReductivity`; and the old canonical-rho
Borel/Steinberg assembly. A type-and-value closure scan of the final theorem
reached none of them.

- Reached: 121,981 constants, of which 28,956 are declared in 2,244 Library
  modules (549 with private names). There were 0 excluded hits and 0
  unresolved constants. The axioms are `propext`, `Classical.choice` and
  `Quot.sound`.
- The excluded names are matched together with their namespaces. The scan
  also excludes the old routes `splitCommonTorusIsomorphism`,
  `splitCommonTorusLeviGluing`, `splitCentralIsogenyExistence`,
  `splitSimplyConnectedCorootSpan`,
  `LeviGluing.algClosedGraphProjectionIsomorphisms` and
  `LeviGluing.SimpleComparisonGraph.weightKernelTrivial`. Other excluded
  routes are the dynamic-quotient properness and flag-quotient existence
  proofs, `steinbergBigCell`, `absoluteBruhatCovering`,
  `isParabolicSubgroup_of_range_eq_dynamicParabolic`, the projective
  torus-fixed-point dimension route and the old rank-one cell construction.
  Every constant declared in the 29 modules that hold these proofs is
  excluded.
- The scanner also reports every reached module whose name refers to the
  old canonical-rho, supplied-rho, highest-weight, Steinberg, Bruhat,
  parabolic-dynamic, regular-cocharacter, projective-Borel or
  geometric-reductivity assemblies. Only `Absolute.RegularCocharacterSolvable`
  and `Absolute.RegularCocharacterWeights` are reached, as discussed below.
- A string-prefix filter flags every reached name that begins with an
  excluded proof name. All 16 such names were inspected and are listed in
  the scanner. They are the three replacement proofs and their direct
  reductions, the conditional reductions above, and three generic
  reductions: `splitRootLieLine_of_rankOne`,
  `splitRankOneRootCell_of_supportLines` and `rootReducedness_of_rankOne`.
  Each of these takes its structural rank-one input as an explicit
  hypothesis, and the scan through it reaches no excluded constant.
- Two reached modules have names containing `RegularCocharacter`:
  `Absolute.RegularCocharacterSolvable` (1 constant,
  `isSolvableGroupScheme_of_isSolvable_points`) and
  `Absolute.RegularCocharacterWeights` (2 constants, `weightSpace_disjoint`
  and `weightSpace_le_weightSpace_cocharacter`). These are generic lemmas on
  solvability of points and weight spaces. Neither uses a regular
  cocharacter Borel subgroup. The same constants are in the
  inventories of the root-datum and root-cell proofs.
- Controls: the same filter catches the old proofs. The closure of the
  existing `splitSimplyConnectedCorootSpan` reaches 78 excluded constants,
  for example `splitCentralIsogenyExistence` → `rootDatumExistence`. The
  closure of `splitCentralIsogenyExistence` reaches 77, that of
  `splitCommonTorusIsomorphism` reaches 60 and that of
  `LeviGluing.algClosedGraphProjectionIsomorphisms` reaches 40.

The Library modules reached through the final theorem include
`SplitLeviGluingFactorInjectivity`, which imports `RootLieLineFromTangent`. The
scan shows that no excluded constant of these imported modules enters the
proof. The scanner source, the per-step witnesses and the full sorted inventory
of the reached Library constants are in the
[dependency audit](SplitNecessityIndependentDependencies.md).

## Provenance

The target is the necessity half of Milne's coroot criterion, Proposition 23.59
(J. S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
printed p.502, PDF p.518), which Milne proves from the Existence Theorem and the
Isogeny Theorem (Corollary 23.56). This module only assembles published Library
results. Its route differs from Milne's in how the structural inputs are
obtained. Root-datum existence (Milne Theorem 21.11), the rank-one root cell
(Conrad, *Reductive group schemes*, source ID
`conrad-2014-reductive-group-schemes`, Theorems 4.1.4 and 4.2.6) and the
one-dimensionality of root spaces (Milne Theorem 21.11(b)) all come from the
rank-one central cover on the ordinary flag variety. None of them comes from the
regular-cocharacter Borel or projective-Borel arguments.
