# The independent split rank-one root-cell proof

`Langlands.GroupScheme.splitRankOneRootCellIndependent` proves the published
`Langlands.GroupScheme.SplitRankOneRootCellStatement.{u}` in every universe `u`.
It retains the arbitrary field, prescribed split maximal torus, supplied root datum
and pairwise integer dependence of actual roots.

The proof applies `splitRankOneRootCell_of_centralCover` to the published theorem
`rankOneCentralCover`. The cover is obtained over algebraically closed fields
from the ordinary Borel quotient. Orbit limits and the two torus-fixed points
give a cell with a one-point complement. The Hartogs argument bounds the dimension
of the quotient by one. The general curve lemmas then bound the dimension of a
dynamic unipotent subgroup using its action on the curve. This gives the local
signed root support and Lie lines needed by the cover construction. The
[cover proof description](RankOneCentralCoverProof.md) gives that argument.

In `splitRankOneRootCell_of_centralCover`, actual root opposition and the explicit
matrix root lines of `SL₂` give the signed support and two weight-space lines after
passing to the algebraic closure. The reduction descends those facts to the
original field via base change of actual characters and weight spaces.
`LocalRankOneRootCell.exists_rootCell_of_support_lines` constructs the two additive
parametrizations with conjugation weights `α` and `−α`. The dynamic triple cell and the Weyl relation
give the open immersion, the unit criterion for cell membership and the product
factorization on every test scheme. The
[reduction description](IndependentRootCellReduction.md) gives those steps.

The implementation composes existing Library results for the statement's original
scope. The statement's literature references are in
[SplitRankOneRootCellStatement.md](SplitRankOneRootCellStatement.md).

## Independence

The cover applies `HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` and
`HomogeneousQuotient.unipotent_dimension_le_one` with the dimension bound and
noncontainment proved on the ordinary Borel quotient. This is the use permitted by
the operator rulings `97eb98d70e9a53ca8ae15ed5b5dc9331` and
`782343fd344b57289118d9dd4b145e89`. The dependencies from `RankOneCellData` provide
affine coordinates and rank-one centralizer calculations. Those from the older
root-cell proof module provide the separate scaling and Weyl-relation lemmas on
supplied local data.

The audit of the final theorem, including its type and the entire cover proof,
visited 115,549 constants. It resolved all 32 required cut names in the environment
and reached zero exclusions. It also checked the prescribed-Borel wrappers, dynamic
quotient properness, and all declarations in the downstream coroot-span reduction
module. The scanner follows the constants in each declaration's type and value,
with opaque values enabled, and requires every reached constant to resolve.
The [full list](SplitRankOneRootCellIndependentDependencies.md) identifies
the 23,939 dependencies declared in Library modules, including their private
declarations.

Terminal check `25c22470-ecd9-4cc3-816f-263ba9107fcd` compiled the proof with
zero errors and warnings. Declaration inspection reported universe `u` and axioms
`propext`, `Classical.choice` and `Quot.sound`. Audit
`fb3a83f9-7e58-4a22-8c92-3fc1ddb1a315` also verified that the types of the final
theorem and its cover input are exactly their respective published propositions
at universe `u`.

## Reproducing the audit

Save this module as `RootCellFinalAudit.lean` in a private draft and check it with
`lean_check` after `Langlands.GroupScheme.Reductive.SplitRankOneRootCellIndependentProof`.
The full diagnostic record contains the sorted dependency names in numbered chunks.
The extra imports let the audit resolve excluded names.

```lean
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellIndependentProof
import Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction
import Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly
import Langlands.GroupScheme.Reductive.RootTangentCurveDimension
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.Reductive.SteinbergBigCellProof
import Langlands.GroupScheme.Reductive.GeometricReductivityProof
import Langlands.GroupScheme.Absolute.BruhatCoveringProof
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.QuotientProperAffineReduction
import Lean

open Lean

private def requiredCuts : Array Name := #[
  `Langlands.GroupScheme.ParabolicDynamicStatement,
  `Langlands.GroupScheme.RegularCocharacterBorelStatement,
  `Langlands.GroupScheme.RankOneSolvableObstructionStatement,
  `Langlands.GroupScheme.RankOneBorelDynamicStatement,
  `Langlands.GroupScheme.RankOnePositiveRootUniquenessStatement,
  `Langlands.GroupScheme.parabolicDynamic,
  `Langlands.GroupScheme.regularCocharacterBorel,
  `Langlands.GroupScheme.rankOneSolvableObstruction,
  `Langlands.GroupScheme.rankOneBorelDynamic,
  `Langlands.GroupScheme.rankOnePositiveRootUniqueness,
  `Langlands.GroupScheme.splitRankOneRootCell,
  `Langlands.GroupScheme.splitRootLieLine,
  `Langlands.GroupScheme.prescribedBorelProjectiveCurveData,
  `Langlands.GroupScheme.HomogeneousQuotient.regularSignedCurveUnipotentDataOfIsConnectedReductive,
  `Langlands.GroupScheme.rankOne_rootTangent_le_one_of_projectiveBorelInputs,
  `Langlands.GroupScheme.rootDatumExistence,
  `Langlands.GroupScheme.rootReducedness,
  `Langlands.GroupScheme.reductiveGeometricReductivity,
  `Langlands.GroupScheme.absoluteBruhatCovering,
  `Langlands.GroupScheme.steinbergBigCell,
  `Langlands.GroupScheme.isParabolicSubgroup_of_range_eq_dynamicParabolic,
  `Langlands.GroupScheme.SplitSimplyConnectedCorootSpanStatement,
  `Langlands.GroupScheme.splitSimplyConnectedCorootSpan,
  `Langlands.GroupScheme.splitCentralIsogenyExistence,
  `Langlands.GroupScheme.splitCommonTorusIsomorphism,
  `Langlands.GroupScheme.LeviGluing.SimpleComparisonGraph.weightKernelTrivial_of_orthogonal_of_rootLieLine,
  `Langlands.GroupScheme.LeviGluing.SimpleComparisonGraph.weightKernelTrivial_of_rootLieLine,
  `Langlands.GroupScheme.LeviGluing.algClosedGraphProjectionIsomorphisms_of_rootLieLine,
  `Langlands.GroupScheme.SplitCorootSpanLineInputs,
  `Langlands.GroupScheme.splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine,
  `Langlands.GroupScheme.splitCentralIsogenyExistence_of_corootSpanLineInputs,
  `Langlands.GroupScheme.splitSimplyConnectedCorootSpan_of_corootSpanLineInputs]

private def routeCuts : Array Name := #[
  `Langlands.GroupScheme.RankOneAlgClosedPositiveRootUniquenessStatement,
  `Langlands.GroupScheme.RootDatumExistenceStatement,
  `Langlands.GroupScheme.RootReducednessStatement,
  `Langlands.GroupScheme.ReductiveGeometricReductivityStatement,
  `Langlands.GroupScheme.ReductiveLinearQuotientAffineStatement,
  `Langlands.GroupScheme.DynamicQuotientProperStatement,
  `Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement,
  `Langlands.GroupScheme.SplitRootLieLineStatement,
  `Langlands.GroupScheme.SplitCentralIsogenyExistenceStatement,
  `Langlands.GroupScheme.SplitCommonTorusIsomorphismStatement,
  `Langlands.GroupScheme.RankOneCellData.rankOne_exists_rootGroup,
  `Langlands.GroupScheme.RankOneCellData.rankOne_exists_oppositeRootGroup,
  `Langlands.GroupScheme.RankOneCellData.rankOneCellData,
  `Langlands.GroupScheme.RankOneCellData.rankOne_exists_cell,
  `Langlands.GroupScheme.RankOneCellData.rankOne_exists_rootCell]

private def routePrefixes : Array String := #[
  "Langlands.GroupScheme.HomogeneousQuotient.positive_roots_eq_of_rankOne_curve_quotient",
  "Langlands.GroupScheme.HomogeneousQuotient.signedCurveUnipotentData",
  "Langlands.GroupScheme.dynamicQuotientProper",
  "Langlands.GroupScheme.reductiveLinearQuotientAffine"]

private def excludedModules : Array Name := #[
  `Langlands.GroupScheme.Absolute.ParabolicDynamicProof,
  `Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof,
  `Langlands.GroupScheme.ProjectiveTorusFixedPointDimension,
  `Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly,
  `Langlands.GroupScheme.Reductive.RankOneCurveCentralizerProof,
  `Langlands.GroupScheme.Reductive.RankOneCurvePositiveRootsProof,
  `Langlands.GroupScheme.Reductive.RootTangentCurveDimension,
  `Langlands.GroupScheme.Reductive.RootReducednessProof,
  `Langlands.GroupScheme.Reductive.GeometricReductivityProof,
  `Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction]

private def moduleOf (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!

private def excluded (env : Environment) (name : Name) : Bool :=
  requiredCuts.any (·.isPrefixOf name) || routeCuts.any (·.isPrefixOf name) ||
    routePrefixes.any (name.toString.startsWith ·) ||
    (moduleOf env name).any (excludedModules.contains ·)

private def rootCellDependencyClosure (env : Environment) (root : Name) :
    IO (Array Name × Array Name) := do
  let mut queue := #[root]
  let mut queued : NameSet := ({} : NameSet).insert root
  let mut cursor := 0
  let mut hits := #[]
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    let some info := env.find? name
      | throw (IO.userError s!"Unresolved reached constant: {name}")
    if excluded env name then
      hits := hits.push name
    let typeDeps := info.type.getUsedConstants
    let valueDeps := (info.value? (allowOpaque := true)).map (·.getUsedConstants)
    for dep in typeDeps ++ valueDeps.getD #[] do
      if !queued.contains dep then
        queued := queued.insert dep
        queue := queue.push dep
  return (queue, hits)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let root := `Langlands.GroupScheme.splitRankOneRootCellIndependent
  let cover := `Langlands.GroupScheme.rankOneCentralCover
  for (name, target) in #[
      (root, `Langlands.GroupScheme.SplitRankOneRootCellStatement),
      (cover, `Langlands.GroupScheme.RankOneCentralCoverStatement)] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    unless info.levelParams == [`u] && info.type == mkConst target [.param `u] do
      throwError "{name} has unexpected universe parameters or type: {info.type}"
  let missing := requiredCuts.filter (fun name => (env.find? name).isNone)
  unless missing.isEmpty do
    throwError "Missing required cut names {missing.toList}"
  let (seen, hits) ← liftIO (rootCellDependencyClosure env root)
  unless hits.isEmpty do
    throwError "Reached exclusions {hits.toList}"
  let library := (seen.filter fun name =>
    name != root && (moduleOf env name).any (fun m => (`Langlands).isPrefixOf m)).qsort
      (fun a b => a.toString < b.toString)
  logInfo m!"ROOT_CELL_AUDIT {seen.size} constants, {library.size} Library dependencies, \
    {requiredCuts.size} required cut names present, {hits.size} exclusions reached"
  for moduleName in #[`Langlands.GroupScheme.Reductive.RankOneCellData,
      `Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof] do
    let names := library.filter (fun name => moduleOf env name == some moduleName)
    logInfo m!"ROOT_CELL_MIXED_MODULE {moduleName} {names.toList}"
  for start in [0:library.size:1000] do
    let chunk := library.extract start (start + 1000)
    logInfo m!"ROOT_CELL_CONSTANTS {start}\n{String.intercalate "\n" (chunk.toList.map Name.toString)}"
```
