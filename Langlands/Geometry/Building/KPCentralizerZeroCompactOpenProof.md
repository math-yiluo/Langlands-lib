# Compact openness of the actual centralizer-zero subgroup

Author: Worker 1450 (task `1e329fd8-983e-4918-852f-587f7106fd44`).

```lean
theorem Langlands.Geometry.Building.ParahoricBuildingData.centralizerZeroCompactOpen
    (P : ParahoricBuildingData G) : P.CentralizerZeroCompactOpenStatement
```

This proves the published target
[`CentralizerZeroCompactOpenStatement`](KPCentralizerZeroCompactOpenStatement.md)
at an arbitrary universe `u`. The theorem has the same binders as the
target: a nonarchimedean local field `F : Type u` with the existing
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances, a group scheme `G` over `Spec F`
whose structure morphism is affine, and an actual
`P : ParahoricBuildingData G`. Its conclusion is the target itself:
`P.centralizerZero` is compact and open as a subset of
`rationalPoints P.centralizer.Z`, in the topology
`rationalPointTopology F P.centralizer.Z.X`. The theorem has no other
hypothesis. Both equal and mixed characteristic are covered, and so is
split rank zero.

## Proof

The proof is the single term

```lean
P.centralizerZeroCompactOpenReduction BruhatTits.Cartan.actualCentralizerStructure
  centralQuotientReductive anisotropicCompactness_proof
  (P.isOpen_centralizerZero derivedCoverTorusProductSmooth
    GaloisNormSmoothnessProof.galoisNormSmoothness)
```

It uses only published Library theorems.

- `ParahoricBuildingData.centralizerZeroCompactOpenReduction`, in
  [`KPCentralizerZeroCompactOpenReduction`](KPCentralizerZeroCompactOpenReduction.md),
  proves `P.CentralizerZeroCompactOpenReductionStatement`. It takes three
  whole statements, `ActualCentralizerStructureStatement.{u}`,
  `CentralQuotientReductiveStatement.{u}` and
  `AnisotropicCompactnessStatement.{u}`, and then openness of
  `P.centralizerZero` in the target's topology. From these it concludes
  `P.CentralizerZeroCompactOpenStatement`. The proof works as follows. The
  three statements make the actual common norm kernel of `Z` compact.
  `Z` is smooth, so its rational points form a topological group. An open
  subgroup of a topological group is closed. `P.centralizerZero` lies in the
  norm kernel, so it is a closed subset of a compact set and is compact.
  The openness half of the conclusion is the openness premise.
- The three whole statements are supplied by these proofs:
  - `Langlands.BruhatTits.Cartan.actualCentralizerStructure`, in
    [`ActualCentralizerStructureProof`](../../BruhatTits/Cartan/ActualCentralizerStructureProof.md).
  - `Langlands.GroupScheme.centralQuotientReductive`, in
    [`CentralQuotientReductiveProof`](../../GroupScheme/Reductive/CentralQuotientReductiveProof.md).
  - `Langlands.GroupScheme.anisotropicCompactness_proof`, in
    [`AnisotropicCompactnessProof`](../../GroupScheme/Rational/AnisotropicCompactnessProof.md).
- The openness premise is supplied by `ParahoricBuildingData.isOpen_centralizerZero`,
  in [`KPZeroOpenness`](KPZeroOpenness.md). That theorem proves openness of
  `P.centralizerZero` with the same local `letI` instances as the target and
  the reduction, so its type matches the reduction's premise exactly. It
  takes two whole statements. Both are supplied by published proofs:
  - `Langlands.GroupScheme.derivedCoverTorusProductSmooth`, in
    [`DerivedCoverTorusProductSmoothProof`](../../GroupScheme/SimplyConnected/DerivedCoverTorusProductSmoothProof.md),
    proves `DerivedCoverTorusProductSmoothStatement.{u}`.
  - `Langlands.GroupScheme.GaloisNormSmoothnessProof.galoisNormSmoothness`, in
    [`GaloisNormSmoothnessProof`](../../GroupScheme/Torus/GaloisNormSmoothnessProof.md),
    proves `GaloisNormSmoothnessStatement.{u}`.

Each statement is used at the universe `u` of the target field. No
additional hypothesis, axiom or `sorry` is introduced, and the target and its
imports are unchanged. The inspection reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal composition of published Library results. The
mathematical route is the one recorded in the target's Markdown, after
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Fact 2.2.3,
Proposition 2.2.12, Lemma 2.6.24 and Lemma 2.6.29. The Markdown of the
modules named above describes how each input is proved.
