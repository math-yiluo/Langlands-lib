# The rational Moy–Prasad family from the maximal unramified extension

Author: Worker 190.

The theorem `Langlands.Geometry.Building.unramifiedRationalMoyPrasad` proves
exactly `Langlands.Geometry.Building.UnramifiedRationalMoyPrasadStatement.{u}`
at arbitrary universe `u`. It retains the published hypotheses: a
nonarchimedean local field `F` of either characteristic, a group scheme `G`
over `Spec F` with affine structure morphism, and
`P : ParahoricBuildingData G` with `P.SatisfiesApartmentAxioms`.
The connected reductive structure is part of `P`.

## Published inputs and implemented construction

The proof applies Worker 87's published reduction
`unramifiedRationalMoyPrasad_of_unramifiedComparison` from
`KPUnramifiedMoyPrasadComparison` to these two published theorems:

| Input | Theorem | Module |
| --- | --- | --- |
| The eight properties of the actual K-level groups | `MaximalUnramified.localMoyPrasadGroupProperties` | `KPLocalMoyPrasadGroupPropertiesProof` |
| Existence of the comparison with the maximal unramified extension | `unramifiedComparisonExistence` | `KPUnramifiedComparisonExistenceProof` |

All declaration names in this account are in
`Langlands.Geometry.Building` unless another namespace is specified.
Both inputs prove their respective published propositions at arbitrary
universe `u`, so the final theorem adds no premise.

For given `F`, `G`, `P` and its apartment axioms, put
`K = UnramifiedClosure F`. The comparison theorem supplies
`B : MaximalUnramified.BuildingData F (baseChanged F K G)`,
`hZ : IsTorus B.centralizer.Z`, `e : P.Apartment → B.Apartment`, and
`hBe : P.IsUnramifiedComparison B hZ e`.
Its published implementation constructs a special torus containing `P.S`
and an `UnramifiedComparisonTorus.ApartmentLift` by
`exists_unramifiedApartmentLift`, using `specialTorusExistence` and
`unramifiedValuationDescent`. The witnesses are the lift's
`buildingData`, `centralizer_isTorus` and `e`. The four published field
proofs `unramifiedComparisonRootField`, `unramifiedComparisonLeviField`,
`unramifiedComparisonZeroField` and `unramifiedComparisonOpenField`
complete this same comparison.

The reduction returns exactly those `B`, `hZ` and `e` and applies
`ParahoricBuildingData.isRationalMoyPrasadFamily_of_unramifiedComparison`
to the group-properties theorem and `hBe`. Thus the constructed family is

```lean
fun y r => (B.moyPrasad hZ (e y) r).comap (rationalExtend F K G)
```

on `rationalPoints G`, with `r : ℝ≥0`. This is
`G(K)_{e(y),r} ∩ G(F)` via the actual rational-extension homomorphism.
The upstairs groups use the existing `MaximalUnramified.BuildingData.moyPrasad`
and its existing torus filtration.

## The ten fields

Write `ι = rationalExtend F K G` and
`j = rationalPoints.map P.centralizer.j`.
The reduction specializes the eight-clause group-properties theorem at
`B` and `hZ`, using clauses 2, 3, 4, 5, 6 and 8. In the following table,
the comparison helper names have prefix
`ParahoricBuildingData.IsUnramifiedComparison`.

| Field | Library results and implemented argument |
| --- | --- |
| `antitone` | `MaximalUnramified.BuildingData.moyPrasad_antitone` gives the upstairs inclusion as depth increases; `Subgroup.comap_mono` pulls it back along `ι`. |
| `filtration_le` | Helper `filtration_le` chooses the closed root set from `hBe.rootComparison`. Its `filtration_mem` puts extended root-filtration elements in the upstairs root-filtration span. `MaximalUnramified.BuildingData.filtration_le_moyPrasad` includes every generator in the upstairs Moy–Prasad group. |
| `commutator_le` | Helper `commutator_le` uses `MaximalUnramified.LocalMoyPrasadCommutator` (clause 3), `Subgroup.commutator_le` and `map_commutatorElement` to pull the upstairs commutator bound back along `ι`. This also includes depth zero. |
| `conj_mem` | Helper `conj_mem` uses the building form of `MaximalUnramified.LocalMoyPrasadEquivariance` (clause 2). `hBe.apartmentMap_smul` identifies `B.apartmentMap (e (n • y))` with `ι(n) • B.apartmentMap (e y)`; homomorphism laws then give the required conjugation membership. |
| `map_mem_of_mul_mem` | At positive depth, helper `map_mem_of_mul_mem` uses `hBe.rootComparison` to place the extended negative, centralizer and positive factors in the negative-root span, pairing-Levi span and positive-root span. `MaximalUnramified.LocalMoyPrasadIwahoriFactorization` (clause 5) gives membership of the middle factor. |
| `comap_eq` | Helper `mem_moyPrasad_of_mem` is applied in both directions. The witness in `hBe.levi` contains `ι(j(Z(F)))` in a pairing-Levi span and gives equality of the root valuations on its zero-pairing roots at all `e y`. The private `rootFiltrationSpan_mono` lemma and `MaximalUnramified.LocalMoyPrasadLeviIntersection` (clause 6) transfer centralizer membership between `e y` and `e y'`. |
| `comap_zero` | The reduction takes `hBe.comap_zero` directly. This is the depth-zero equality with `P.centralizerZero`, supplied by the published comparison-existence proof. |
| `iInf_comap` | Helper `iInf_comap` applies `MaximalUnramified.LocalMoyPrasadSeparated` (clause 8) to an element lying in every upstairs group. The private injectivity lemmas for `ι` and `j`, proved using `GaloisPoint.extend_injective` and `CategoryTheory.cancel_mono`, then show that the centralizer element is the identity. |
| `mem_filtrationBlock` | Helper `mem_filtrationBlock` uses `hBe.rootComparison` and `MaximalUnramified.LocalMoyPrasadRootIntersection` (clause 4) to obtain membership in the upstairs root-filtration span. Its `block_mem` field descends this to `P.apartment.filtrationBlock y (fun _ => (t : ℝ)) a.1`. |
| `isOpen` | The reduction takes `hBe.isOpen` directly, with exactly the affine instances and topology `rationalPointTopology F P.centralizer.Z.X` specified by `IsRationalMoyPrasadFamily`, at every nonnegative depth. |

The block in `mem_filtrationBlock` is `U_(a,y,t) U_(2a,y,t)`,
with both factors at the common depth `t`. This retains the doubled-root
convention of the statement and its comparison proof. The
`filtration_le` argument also retains the root-comparison bound at every
nonnegative depth. The comparison proof supplies the depth-zero equality
and openness; they are not inferred from the K-level group properties.

## Provenance

This proof is a derived composition of published Library theorems.
Worker 87 supplied the comparison reduction. The K-level theorem is the
published assembly of the group-property proofs described in
[KPLocalMoyPrasadGroupPropertiesProof.md](KPLocalMoyPrasadGroupPropertiesProof.md);
Worker 188 supplied the comparison-existence assembly described in
[KPUnramifiedComparisonExistenceProof.md](KPUnramifiedComparisonExistenceProof.md).
The field table above follows the implemented Lean reduction.

The source correspondence to Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §9.8, Lemma 9.8.1 and Proposition 9.8.3
(printed pp. 374–376, PDF pp. 405–407), is documented in the unchanged
[target pair](KPUnramifiedRationalMoyPrasadStatement.md) and
[comparison reduction](KPUnramifiedMoyPrasadComparison.md).
Those accounts give the underlying §7.3 group results, Lemma 8.5.19,
Proposition 13.2.5 and the apartment descent of §9.6.
The comparison-existence proof documents its use of the 2024 corrections
and the implemented fixed-apartment construction. This composition
introduces no further source claim and preserves the published target
and all its hypotheses.
