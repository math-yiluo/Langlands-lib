# Split root Lie lines via the rank-one central cover

`Langlands.GroupScheme.splitRootLieLine_independent` proves
`Langlands.GroupScheme.SplitRootLieLineStatement.{u}`. Over any field
`k : Type u`, for a prescribed split maximal torus `i : T.toGrp ⟶ G` of a
connected reductive group and an actual root `χ ∈ roots i`, the theorem
gives `Nonempty (k ≃ₗ[k] weightSpace i χ)`.

## Implemented proof

The Lean proof applies `splitRootLieLine_of_centralCover` to
`rankOneCentralCover`. The reduction chooses a cocharacter that pairs to
zero with `χ` and whose centralizer has pairwise dependent roots.
`dynamicCentralizerReductive` proves connected reductivity of this centralizer
by the unipotent-envelope and centralizer-intersection argument. The prescribed
torus remains maximal there, and the centralizer differential identifies its
`χ`-space with the original `χ`-space.

For the rank-one step, the reduction extends the group, torus and root to
the algebraic closure. The cover theorem supplies a central isogeny from
`SL₂ × C` to the base-changed centralizer and a compatible isogeny of split
tori. The latter pulls back the character. The differential of the group
isogeny transfers the explicit `SL₂` matrix line on that nonzero weight.
`weightSpace_line_baseChange_iff` reflects existence of a line to `k`,
where centralizer transport gives the desired equivalence.

The cover proof obtains a proper ordinary flag quotient `G/B` with the
prescribed torus in `B`. Białynicki-Birula limits, the classification of
torus-fixed points and Hartogs extension bound the dimension of the
quotient by one. The general curve kernel lemmas apply to this bound and
to the independently proved noncontainment of the dynamic unipotent in
`B`. The tangent bound and Weyl symmetry give the two signed root lines.
Those lines give a root cell and a coroot, from which the cover proof
constructs the isogeny with the full scheme-theoretic central kernel and
the compatible torus map.

## Provenance

This is an internal assembly of the rank-one cover theorem, its
root-line reduction, and the centralizer and scalar-extension comparisons.
The statement pair records the comparison with Conrad, *Reductive group
schemes*, §5.1. The proof of the geometric cover records the original-source
comparisons for the cell and central isogeny. See
[the statement](SplitRootLieLineStatement.md) and
[the cover proof](RankOneCentralCoverProof.md).

## Dependency audit

The audit starts at `splitRootLieLine_independent` and checks that its
type is exactly `SplitRootLieLineStatement.{u}` with one universe
parameter `u`. It follows the types and values of every reachable
constant, including opaque proof values. The scan checks all 24 named
exclusions of the dynamic-Borel inputs that this proof avoids, additional projective-Borel and downstream
consumers, and the declaring modules of the excluded routes. It also
verifies that the ordinary flag quotient, the curve dimension and kernel
lemmas, and the centralizer and scalar-extension comparisons occur in the
closure.

The check at Library commit `ba9d1e9ac8e4b6f239a8bbf0ba15e6743fd140c9`
used the published reduction and cover. In the pinned Lean environment,
`lean_check` reports zero errors and warnings.
The exact type and universe check passed. The scan visited 115,484 constants,
including 23,937 declared in 1,876 Langlands modules. It found zero excluded
or missing dependencies and reached every required declaration.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

Two modules contain upstream facts about supplied data. In
`RankOneCellData`, `latticePairing_ne_zero_of_rankOne` is an integer lattice
calculation, and `rankOne_centralizer_isRepresentedBy` uses it with
`dynamicCentralizerReductive` and the description of centralizer roots.
The `lineCoordinates` declarations use a supplied freely generating
additive coordinate. In `SplitRankOneRootCellProof`, `WeylData.isRootCell`
uses supplied open-cell and Weyl-point data together with the rescaling
of the negative root group. `RankOneLocalRootCell.exists_isRootCell`
constructs those data from the local facts proved in the cover argument.
The audit traverses these declarations and their generated auxiliaries
and checks every other declaration from those modules as an exclusion. It
reached 17 declarations in `RankOneCellData` and 28 in
`SplitRankOneRootCellProof`, all from the supplied-data families.

The geometric input has a separate audit with its route and Library
dependency inventory.
[Rank-one central cover dependency audit](../../../notes/group-schemes/rank-one-central-cover-dependency-audit.md).

## Reproducing the audit

Save the following script as `AuditSplitRootLieLineIndependent.lean` and
run `lean_check` on
`Langlands.GroupScheme.Reductive.SplitRootLieLineIndependentProof` followed
by `AuditSplitRootLieLineIndependent` in the pinned Lean environment.

<details>
<summary>Lean dependency scanner</summary>

```lean
import Langlands.GroupScheme.Reductive.SplitRootLieLineIndependentProof
import Lean

-- Audit at Library commit ba9d1e9ac8e4b6f239a8bbf0ba15e6743fd140c9.
open Lean Elab Command

set_option maxHeartbeats 30000000

private def hasExcludedComponent (excluded : Std.HashSet String) : Name → Bool
  | .anonymous => false
  | .str parent component => excluded.contains component || hasExcludedComponent excluded parent
  | .num parent _ => hasExcludedComponent excluded parent

run_cmd do
  let env ← getEnv
  let root := `Langlands.GroupScheme.splitRootLieLine_independent
  let target := `Langlands.GroupScheme.SplitRootLieLineStatement
  let some proof := env.find? root | throwError "Missing proof {root}"
  unless proof.levelParams == [`u] && proof.type == mkConst target [.param `u] do
    throwError "The theorem must have the exact target type at universe u"
  let forbiddenNames : Std.HashSet String := Std.HashSet.ofList [
    "ParabolicDynamicStatement", "RegularCocharacterBorelStatement",
    "RankOneSolvableObstructionStatement", "RankOneBorelDynamicStatement",
    "RankOnePositiveRootUniquenessStatement", "parabolicDynamic",
    "regularCocharacterBorel", "rankOneSolvableObstruction", "rankOneBorelDynamic",
    "rankOnePositiveRootUniqueness", "splitRootLieLine", "splitRankOneRootCell",
    "rootLieLine_of_twoStructuralInputs", "rootLieLine_of_dynamicCentralizerReductive",
    "absoluteRootTangent_le_one_of_structuralInputs",
    "rankOne_rootTangent_le_one_of_projectiveBorelInputs",
    "prescribedBorelProjectiveCurveData", "regularSignedCurveUnipotentDataOfIsConnectedReductive",
    "rootDatumExistence", "rootReducedness", "reductiveGeometricReductivity",
    "absoluteBruhatCovering", "steinbergBigCell",
    "isParabolicSubgroup_of_range_eq_dynamicParabolic",
    "RankOneAlgClosedPositiveRootUniquenessStatement",
    "ProjectiveTorusFixedPointDimensionStatement", "projectiveTorusFixedPointDimension",
    "positive_roots_eq_of_rankOne_curve_quotient", "signedCurveUnipotentData",
    "positive_roots_eq_of_prescribedBorel_of_projectiveFixedPoints",
    "rankOneAlgClosedPositiveRootUniqueness_of_projectiveBorelInputs",
    "rankOnePositiveRootUniqueness_of_projectiveBorelInputs", "DynamicQuotientProperStatement",
    "dynamicQuotientProper", "ReductiveLinearQuotientAffineStatement",
    "reductiveLinearQuotientAffine", "RootDatumExistenceStatement", "RootReducednessStatement",
    "ReductiveGeometricReductivityStatement", "SplitRankOneRootCellStatement",
    "rankOne_exists_rootCell", "rankOne_exists_cell", "rankOne_exists_rootGroup",
    "rootDatumExistence_of_rankOneReducedness", "splitRankOneRootCell_of_centralCover",
    "SplitSimplyConnectedCorootSpanStatement", "splitSimplyConnectedCorootSpan",
    "SplitCommonTorusIsomorphismStatement", "SplitCentralIsogenyExistenceStatement",
    "algClosedGraphProjectionIsomorphisms", "splitCommonTorusIsomorphism",
    "splitCentralIsogenyExistence"]
  let forbiddenModules : Std.HashSet Name := Std.HashSet.ofList [
    `Langlands.GroupScheme.Absolute.ParabolicDynamicProof,
    `Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof,
    `Langlands.GroupScheme.Absolute.RankOneSolvableProof,
    `Langlands.GroupScheme.Absolute.BruhatCoveringProof,
    `Langlands.GroupScheme.Absolute.DynamicParabolicRecognition,
    `Langlands.GroupScheme.ProjectiveTorusFixedPointDimension,
    `Langlands.GroupScheme.Reductive.GeometricReductivityProof,
    `Langlands.GroupScheme.Reductive.RankOneBorelDynamicProof,
    `Langlands.GroupScheme.Reductive.RankOneCellData,
    `Langlands.GroupScheme.Reductive.RankOneCurveCentralizerProof,
    `Langlands.GroupScheme.Reductive.RankOneCurvePositiveRootsProof,
    `Langlands.GroupScheme.Reductive.RankOnePositiveRootProof,
    `Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly,
    `Langlands.GroupScheme.Reductive.RootLieLineFromTangent,
    `Langlands.GroupScheme.Reductive.RootDatumExistence,
    `Langlands.GroupScheme.Reductive.RootReducednessProof,
    `Langlands.GroupScheme.Reductive.RootTangentCurveDimension,
    `Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof,
    `Langlands.GroupScheme.Reductive.SplitRootLieLineProof,
    `Langlands.GroupScheme.Reductive.SteinbergBigCellProof,
    `Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction]
  -- These two modules also contain upstream lemmas stated for supplied data.
  -- Their types and values are traversed in the same way as every other declaration.
  let suppliedData : Array (Name × Array Name) := #[
    (`Langlands.GroupScheme.Reductive.RankOneCellData, #[
      `Langlands.GroupScheme.rankOne_centralizer_isRepresentedBy,
      `Langlands.GroupScheme.latticePairing_ne_zero_of_rankOne,
      `Langlands.GroupScheme.RankOneCellData.lineCoordinates,
      `Langlands.GroupScheme.RankOneCellData.isNaturalVectorCoordinates_lineCoordinates,
      `Langlands.GroupScheme.RankOneCellData.lineValue_act,
      `Langlands.GroupScheme.RankOneCellData.lineValue,
      `Langlands.GroupScheme.RankOneCellData.lineValue_unit_comp,
      `Langlands.GroupScheme.RankOneCellData.lineValue_eq,
      `Langlands.GroupScheme.RankOneCellData.pointsEquiv_unit_comp,
      `Langlands.GroupScheme.RankOneCellData.lineValue_mul,
      `Langlands.GroupScheme.RankOneCellData.lineValue_bijective,
      `Langlands.GroupScheme.RankOneCellData.unit_appTop_eq]),
    (`Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof, #[
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.isRootCell,
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.unitβ,
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.relationOver_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.not_inCell_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.conj_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.isOpenImmersion_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.comp_xp,
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.comp_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.tripleCell_xm',
      `Langlands.GroupScheme.RankOneRootCellRelation.WeylData.pb.eq_1,
      `Langlands.GroupScheme.RankOneRootCellRelation.scaleIso,
      `Langlands.GroupScheme.RankOneRootCellRelation.scaleEquiv,
      `Langlands.GroupScheme.RankOneRootCellRelation.scaleEquiv_naturality,
      `Langlands.GroupScheme.RankOneRootCellRelation.comp_scaleIso_hom,
      `Langlands.GroupScheme.RankOneRootCellRelation.instIsIsoOverSchemeSpecOfHomHomGrpMonHomScaleIso,
      `Langlands.GroupScheme.RankOneRootCellRelation.crd_weightPointAction,
      `Langlands.GroupScheme.RankOneRootCellRelation.appTop_pb,
      `Langlands.GroupScheme.RankOneRootCellRelation.gpt_crd,
      `Langlands.GroupScheme.RankOneRootCellRelation.crd_gpt,
      `Langlands.GroupScheme.RankOneRootCellRelation.pb_mul,
      `Langlands.GroupScheme.RankOneRootCellRelation.pb_one,
      `Langlands.GroupScheme.RankOneRootCellRelation.crd_mul])]
  let mut queue := #[root]
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut langlandsCount := 0
  let mut langlandsModules : Std.HashSet Name := {}
  let mut suppliedDataCounts : Std.HashMap Name Nat := {}
  let mut hits : Array (Name × Option Name) := #[]
  let mut missing : Array Name := #[]
  let mut index := 0
  while index < queue.size do
    let name := queue[index]!
    index := index + 1
    let sourceModule := (env.getModuleIdxFor? name).map
      (fun i => env.header.moduleNames[i.toNat]!)
    if let some moduleName := sourceModule then
      if (`Langlands).isPrefixOf moduleName then
        langlandsCount := langlandsCount + 1
        langlandsModules := langlandsModules.insert moduleName
      if forbiddenModules.contains moduleName then
        let allowed := suppliedData.any fun (m, names) =>
          m == moduleName && names.any (·.isPrefixOf name)
        if allowed then
          suppliedDataCounts := suppliedDataCounts.insert moduleName
            (suppliedDataCounts[moduleName]?.getD 0 + 1)
        else
          hits := hits.push (name, sourceModule)
    if hasExcludedComponent forbiddenNames name then
      hits := hits.push (name, sourceModule)
    if let some declaration := env.find? name then
      let dependencies := declaration.type.getUsedConstants ++
        ((declaration.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      for dependency in dependencies do
        unless seen.contains dependency do
          seen := seen.insert dependency
          queue := queue.push dependency
    else
      missing := missing.push name
  logInfo m!"AUDIT {root}: total={seen.size}, Langlands={langlandsCount}, Langlands modules={langlandsModules.size}, forbidden={hits}, missing={missing}"
  for (moduleName, _) in suppliedData do
    logInfo m!"AUDIT supplied-data dependencies in {moduleName}: {suppliedDataCounts[moduleName]?.getD 0}"
  unless hits.isEmpty && missing.isEmpty do
    throwError "Incomplete or forbidden dependency closure for {root}"
  for required in #[
      `Langlands.GroupScheme.rankOneCentralCover,
      `Langlands.GroupScheme.splitRootLieLine_of_centralCover,
      `Langlands.GroupScheme.splitRootLieLine_of_rankOne,
      `Langlands.GroupScheme.dynamicCentralizerReductive,
      `Langlands.GroupScheme.Dynamic.weightSpaceEquiv_torusFactor,
      `Langlands.GroupScheme.IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint,
      `Langlands.GroupScheme.RankOneFlag.CoreData.topologicalKrullDim_le_one,
      `Langlands.GroupScheme.RankOneFlag.CoreData.finrank_tangent_le_one,
      `Langlands.GroupScheme.HomogeneousQuotient.curveUnipotentDataOfPseudoReductive,
      `Langlands.GroupScheme.HomogeneousQuotient.unipotent_dimension_le_one,
      `Langlands.GroupScheme.RankOneLocalCover.localLineCrux,
      `Langlands.GroupScheme.RankOneCentralCover.rootLineOfCover_isogeny,
      `Langlands.GroupScheme.weightSpace_line_baseChange_iff] do
    unless seen.contains required do
      throwError "Expected route declaration {required} absent from closure"

#print axioms Langlands.GroupScheme.splitRootLieLine_independent
```

</details>
