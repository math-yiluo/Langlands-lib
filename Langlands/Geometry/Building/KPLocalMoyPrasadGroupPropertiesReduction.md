# Conditional assembly of the K-level Moy–Prasad group properties

This internal proof module assembles all eight clauses of
`Langlands.Geometry.Building.MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement`.
It works at arbitrary universe `u`, for every characteristic of the local
field `F`, with the published groups `B.moyPrasad hZ x r` over
`K = UnramifiedClosure F`. It changes neither the groups nor the target statement.

The results in this module retain explicit hypotheses. The final adapter uses
the published coordinate, positive-product and depth-zero theorems and retains
`QuasiSplitLocalTorusFiltrationStatement` as its argument. The companion `KPLocalMoyPrasadGroupPropertiesProof` supplies
that argument with the published `quasiSplitLocalTorusFiltration` theorem.

## Inputs and scope

For fixed `B : MaximalUnramified.BuildingData F H` and
`hZ : IsTorus B.centralizer.Z`,
`BuildingData.localMoyPrasadGroupProperties_of_estimates` takes:

- `hS1 : QuasiSplitLocalTorusFiltrationStatement`, the published proposition (KP
  Lemma 7.2.3 over `K`).
  Its first two clauses give `B.LocalTorusCommutatorFriendly hZ` and
  `B.LocalTorusRootCompatible hZ` by definitional equality.
- `hProd : LocalMoyPrasadPositiveProductStatement`, the published proposition
  providing the positive-depth sign product cover from ordinary commutator
  friendliness.
- `hZ2 : B.LocalTorusDoubleRootCommutatorFriendly hZ`, the independent
  doubled-root middle-coordinate estimate at depth `2r`, including either
  possible doubled input.
- `hDZa`, equality of the positive-root subgroup intersection with the
  positive-root filtration span at depth zero, for every generic integral
  cocharacter.
- `hDZb`, containment of the pairing Levi intersection at depth zero in the
  join of the depth-zero torus image and zero-pairing root filtration span.

The last two inputs are the two clauses of the published
`LocalMoyPrasadDepthZeroStatement`, proved in `KPLocalMoyPrasadDepthZeroProof`.
The doubled-root input is definitionally the specialization of
the published `KPLocalDoubleRootCommutatorStatement`, proved in
`KPLocalDoubleRootCommutatorProof`. The two proposition definitions supply no proofs
of these inputs.

`localMoyPrasadGroupProperties_of_pointwise_estimates` has the exact global
`LocalMoyPrasadGroupPropertiesStatement` as its conclusion. In addition to `hS1` and `hProd`, it takes
`hEstimates`, which quantifies the preceding doubled-root and depth-zero facts
over every `F`, `H`, `B` and `hZ`. It specializes that argument and applies the
fixed-building assembly theorem. It introduces no additional mathematical
construction or predicate.

`localMoyPrasadGroupProperties_of_statements` is an adapter with four global
propositions as explicit hypotheses: `QuasiSplitLocalTorusFiltrationStatement`,
`LocalMoyPrasadPositiveProductStatement`,
`KPLocalDoubleRootCommutatorStatement` and `LocalMoyPrasadDepthZeroStatement`.
It specializes the last two at `F`, `H`, `B` and `hZ`, splits the depth-zero
conjunction, and applies the fixed-building assembly. Its conclusion is the
exact global `LocalMoyPrasadGroupPropertiesStatement.{u}`. This remains an
implication, not an unconditional theorem.

`localMoyPrasadGroupProperties_of_remaining_statements` takes only the three
remaining global propositions: `QuasiSplitLocalTorusFiltrationStatement`,
`KPLocalDoubleRootCommutatorStatement` and `LocalMoyPrasadDepthZeroStatement`.
It supplies the product argument of the preceding adapter with the published
`MaximalUnramified.localMoyPrasadPositiveProduct` theorem from
`KPLocalMoyPrasadPositiveProductProof`. Thus the product proposition
is discharged without a new premise. The conclusion remains the exact
`LocalMoyPrasadGroupPropertiesStatement` at arbitrary universe `u`, conditional on the three named inputs.

`localMoyPrasadGroupProperties_of_torus_statements` takes only
`QuasiSplitLocalTorusFiltrationStatement` and
`KPLocalDoubleRootCommutatorStatement`. It supplies the depth-zero argument of
the preceding adapter with the published
`MaximalUnramified.localMoyPrasadDepthZero` theorem from
`KPLocalMoyPrasadDepthZeroProof`. Its conclusion is the exact
`LocalMoyPrasadGroupPropertiesStatement` at arbitrary universe `u`, conditional on those two torus inputs.
The three-input adapter is retained for callers supplying depth-zero results
explicitly.

`localMoyPrasadGroupProperties_of_torus_filtration` takes only
`QuasiSplitLocalTorusFiltrationStatement.{u}`. It applies the preceding adapter
and supplies its doubled-root argument by composing the published
`kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates` from
`RankOneDoubledInputCoroot` with the published
`quasiSplitValuedRankOneCoordinates` from
`QuasiSplitValuedRankOneCoordinatesProof`. The former theorem
transports the unitary pivot computation to the actual centralizer filtration
at depth `2r`, and the latter provides the coherent valued coordinates without
an additional hypothesis. This discharges the doubled-root proposition and
leaves `QuasiSplitLocalTorusFiltrationStatement` as the sole explicit antecedent. It
uses no conclusion of `LocalMoyPrasadGroupPropertiesStatement` in deriving
that estimate and does not introduce a separate doubled-root proof wrapper.

## Implemented proof, clause by clause

1. Normality comes from
   `BuildingData.localMoyPrasadNormality_of_torus_commutator_bounds`
   in `KPLocalMoyPrasadDoubleRootConjugation`, using the first two clauses of
   `QuasiSplitLocalTorusFiltrationStatement`
   and `hZ2`.
2. Both forms of equivariance come from
   `BuildingData.localMoyPrasadEquivariance_of_torus_commutator_bounds`
   in that module, with the same inputs. Its normalizer step uses the
   unconditional torus-filtration stability theorem
   `BuildingData.centralizerTorusImage_isNormalizerStable` from
   `KPLocalCentralizerFiltrationNormalizerStable`.
3. The commutator bound comes from
   `BuildingData.localMoyPrasadCommutator_of_torus_commutator_bounds`
   in `KPLocalMoyPrasadCommutator`, again with those three pointwise inputs.
4. Root intersections come from `BuildingData.rootIntersection_of_covers`.
5. Iwahori factorization comes from
   `BuildingData.iwahoriFactorization_of_productCover`.
6. Levi intersections come from `BuildingData.leviIntersection_of_covers`.
7. Centralizer intersections come from
   `BuildingData.centralizerIntersection_of_covers`.
8. Separation comes from `BuildingData.separated_of_productCover`.

Clauses 4–8 are supplied together by
`BuildingData.intersectionClauses_of_statements` in
`KPLocalMoyPrasadIntersectionAssembly`. It obtains the product cover by applying
`hProd` to the first clause of `QuasiSplitLocalTorusFiltrationStatement`, then uses `hDZa` for clause 4 and `hDZb` for
clauses 6–7. Clauses 5 and 8 need only that cover. The detailed algebraic proofs
are documented in the imported companion modules; this module only specializes
the input propositions and joins their conclusions.

## Provenance and final composition

The source targets are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 7.3.17, Remark 7.6.5 and (7.6.2), Proposition 13.2.5(4),
Lemma 7.3.11 and Proposition 7.3.12, Lemma 8.5.19, and Lemma 7.3.16.
The registered 2024 corrections qualify the Chapter 7 apartment hypotheses.
This assembly adds no apartment premise: the imported conditional proofs use
the actual integer-valuation building data and prove the needed root-system
facts there.

The assembly follows the companion modules, including the torus-normalizer proof
in `KPLocalCentralizerFiltrationNormalizerStable`. It is a derived internal
reduction rather than a separately numbered source result. The positive-product
and depth-zero propositions have published proofs. The doubled-root estimate
follows from the published coherent valued coordinates and the published
conditional rank-one reduction. The final proof module supplies
`QuasiSplitLocalTorusFiltrationStatement` using the
published `quasiSplitLocalTorusFiltration` theorem from
`KPQuasiSplitLocalTorusFiltrationProof` and obtains the unconditional
`LocalMoyPrasadGroupPropertiesStatement`.
