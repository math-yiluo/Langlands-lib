# Declaration dependencies of the graded associativity and unit theorem

This page lists the Library declarations reached from
`Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` through
declaration types and values. The paired proof account explains the main
dependency paths. [Proof of associativity and the unit laws](LocalFieldGradedAssociativeUnitProof.md)

## Method

The scan starts at the theorem and runs a breadth-first search. For each
constant reached, `Lean.ConstantInfo.getUsedConstantsAsSet` collects the
constants in its type and value, including theorem proofs and opaque values.
For inductive types and recursors this function also lists the constructors
and constituent inductive types, respectively. A Library constant is defined
in a module whose name starts with `Langlands`. The scan identifies such
modules with `Lean.Environment.getModuleIdxFor?` and expands their constants.
Names from packages such as Lean and Mathlib form the boundary of the scan.

The scan reaches 3,723 constants in all, 1,482 of them Library constants defined in
131 modules. The declaration counts include the starting theorem. There are
1,016 Library theorems, 453 definitions, 6 inductive types, 6 constructors
and 1 recursor. The list includes 154 private declarations and the
auxiliary declarations Lean generates, such as `_proof_` lemmas, `match_` functions, `eq_`
equation lemmas and `_simp_` lemmas. A private declaration is shown below by
its name inside its module with the mark “private”. Its full Lean name is
`_private.<module>.0.<name>`.

Sorted by Unicode code points with their full Lean names, one per line in
UTF-8 with a final newline, the 1,482 names have SHA-256
`043aa9131dd4ec7a05adc98fc1430cbe50316832f3fa164a1e0fd622917d2023`.

Lean's axiom check of the theorem reports exactly `propext`,
`Classical.choice` and `Quot.sound`.

## Reproducing the scan

The following diagnostic imports the proof and runs the traversal in Lean
4.35.0. Its information message gives the counts, a tab-separated line
`<module>\t<name>` for each Library constant sorted by name, and a line
`<module>\t<name>\t<parent>` for the first dependency edge into each module.

```lean
import Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitProof

open Lean

namespace LocalFieldGradedAssociativeUnitScan

/-- The module defining a constant, or the anonymous name. -/
def definingModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- A constant of a module whose name begins with `Langlands`. -/
def isLibrary (env : Environment) (n : Name) : Bool :=
  (`Langlands).isPrefixOf (definingModule env n)

/-- Breadth-first closure of `root` under the constants of types and values
(theorem proofs and opaque values included), visiting the constants used by a
declaration in alphabetical order; only Library constants are expanded. The
result lists the constants in the order reached, each with the constant that
first used it. -/
def reached (env : Environment) (root : Name) : Array (Name × Name) := Id.run do
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × Name) := #[(root, .anonymous)]
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!.1
    i := i + 1
    if !isLibrary env n then continue
    let some ci := env.find? n | continue
    let used := ci.getUsedConstantsAsSet.toList.toArray.qsort
      fun a b => a.toString < b.toString
    for m in used do
      if !seen.contains m then
        seen := seen.insert m
        queue := queue.push (m, n)
  return queue

#eval show CoreM Unit from do
  let env ← getEnv
  let all := reached env `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit
  let lib := all.filter fun p => isLibrary env p.1
  let names := (lib.map (·.1)).qsort fun a b => a.toString < b.toString
  let mut modules : NameSet := {}
  let mut firsts : Array String := #[]
  for (n, parent) in lib do
    let m := definingModule env n
    if !modules.contains m then
      modules := modules.insert m
      firsts := firsts.push s!"{m}\t{n}\t{parent}"
  IO.println s!"{all.size} constants reached, {names.size} Library constants in {modules.size} modules"
  IO.println (String.intercalate "\n" (names.toList.map fun n => s!"{definingModule env n}\t{n}"))
  IO.println (String.intercalate "\n" firsts.toList)

end LocalFieldGradedAssociativeUnitScan
```

## How each module is reached

The table follows the order in which the breadth-first scan encounters the
defining modules. Each row gives the first declaration encountered in that
module and the declaration from which the scan reached it. The parent
column uses full Lean names, including the module in private names.

| Module | First declaration reached | Used by |
| --- | --- | --- |
| `Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitProof` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` | (start of the scan) |
| `Langlands.AllFieldBZ.LocalField.Definitions` | `Langlands.AllFieldBZ.LocalFieldPackage` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Representation.Aubert.LocalFieldBinaryProductExactLengthStatement` | `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Representation.Aubert.LocalFieldGradedGrothendieck` | `Langlands.Aubert.LocalFieldGraded.GradedGrothendieckGroup` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitStatement` | `Langlands.Aubert.LocalFieldGraded.LocalFieldGradedAssociativeUnitStatement` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Representation.Aubert.LocalFieldGradedInductionUnit` | `Langlands.Aubert.LocalFieldGraded.multiplication_unit_left` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Group.GL.Basic` | `Langlands.GeneralLinear` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.Representation.Smooth.FiniteLengthGrothendieck` | `Langlands.GeneralLinear.FiniteLengthGrothendieckGroup` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.LocalField.LocalFieldData` | `Langlands.LocalFieldData.topology` | `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit` |
| `Langlands.AllFieldBZ.Representation.Induction.BinaryProduct` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor` | `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement` |
| `Langlands.Representation.Category.Basic` | `Langlands.SmoothRep` | `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement` |
| `Langlands.Representation.Smooth.FiniteLengthGrothendieckBilinear` | `Langlands.SmoothRep.PreservesFiniteLengthShortExactLeft` | `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement` |
| `Langlands.VirtualRepresentation.Integral` | `Langlands.VirtualRepresentation.IntegralLattice` | `Langlands.SmoothRep.FiniteLengthPresentation` |
| `Langlands.Representation.Smooth.Definitions` | `Langlands.IsSmooth` | `Langlands.smoothRepProperty` |
| `Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` | `_private.Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitProof.0.Langlands.Aubert.LocalFieldGraded.assoc_on_objects` |
| `Langlands.Representation.Induction.BinaryProduct` | `Langlands.BinaryTensor.compEquiv` | `_private.Langlands.Representation.Aubert.LocalFieldGradedInductionUnit.0.Langlands.Aubert.LocalFieldGraded.leftUnit_object` |
| `Langlands.Representation.Tensor.OneFactor` | `Langlands.BinaryTensor.secondFactor` | `_private.Langlands.Representation.Aubert.LocalFieldGradedInductionUnit.0.Langlands.Aubert.LocalFieldGraded.leftUnit_object` |
| `Langlands.Representation.Derivative.ProductDerivativesFiniteLength` | `Langlands.Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_finiteDimensional` | `Langlands.Aubert.LocalFieldGraded.unitObject_hasFiniteLength` |
| `Langlands.AllFieldBZ.Representation.Induction.BlockFactors` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInductionFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor` |
| `Langlands.Group.GL.MirabolicOppositeIntersection` | `Langlands.GeneralLinear.BlockShape.binary` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor` |
| `Langlands.Group.GL.Blocks` | `Langlands.GeneralLinear.BlockShape.length` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor` |
| `Langlands.Group.GL.RankReindex` | `Langlands.GeneralLinear.reindex_finCongr_rfl` | `Langlands.Aubert.LocalFieldGraded.inclusion_eq_of_rank_equiv` |
| `Langlands.Representation.Smooth.IrreducibleRealization` | `Langlands.SmoothRep.IrreducibleIsoClass` | `Langlands.Aubert.LocalFieldGraded.inclusion_zero_eq_smul` |
| `Langlands.Representation.Smooth.IrreducibleGrothendieckProof` | `Langlands.SmoothRep.irreducibleGrothendieckStatement` | `Langlands.Aubert.LocalFieldGraded.inclusion_zero_eq_smul` |
| `Langlands.AllFieldBZ.Representation.Induction.BlockEquivalence` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInducedEquiv` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.AllFieldBZ.Group.GL.BlockModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Induction.BlockFactors` | `Langlands.GeneralLinear.BlockShape.blockTensor` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Group.GL.SingleBlock` | `Langlands.GeneralLinear.BlockShape.rankCast` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Induction.Definitions` | `Langlands.Induction.SmoothFunctions` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly` | `Langlands.Parabolic.equivPrecomp` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Parabolic.RegroupingFactorEquivalences` | `Langlands.Parabolic.threeBlockSmoothFamily` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry` | `Langlands.Parabolic.threeBlocks` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Shahidi.Induction` | `Langlands.Shahidi.pairCarrier` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Shahidi.TwoBlocks` | `Langlands.Shahidi.twoBlocks` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Smooth.SmoothPart.Definitions` | `Langlands.smoothVectors` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.Representation.Twist.Definitions` | `Langlands.twist` | `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv` |
| `Langlands.AllFieldBZ.Representation.Induction.Parabolic` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInductionFunctor` |
| `Langlands.Representation.Smooth.IrreducibleCompositionFactors` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap` | `Langlands.SmoothRep.irreducibleGrothendieckStatement` |
| `Langlands.Representation.Smooth.IrreducibleGrothendieckStatement` | `Langlands.SmoothRep.IrreducibleGrothendieckStatement` | `Langlands.SmoothRep.irreducibleGrothendieckStatement` |
| `Langlands.Representation.Induction.BlockEquivalence` | `Langlands.GeneralLinear.BlockShape.productInducedOfEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInducedEquiv` |
| `Langlands.Representation.Tensor.Finite` | `Langlands.FiniteTensor.external` | `Langlands.GeneralLinear.BlockShape.blockTensor` |
| `Langlands.AllFieldBZ.Representation.Parabolic.ThreeBlockRegroupingAssembly` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInductionObjEquiv` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.pairProductEquiv` |
| `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge` | `Langlands.Classification.BinaryProductBridge.binary_eq_twoBlocks` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.pairProductEquiv` |
| `Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement` | `Langlands.Classification.twoBlockFactors` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.pairProductEquiv` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RegroupingFactorEquivalences` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.regroupLeftPair` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `Langlands.isSmooth_comp` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorObj._proof_1` |
| `Langlands.AllFieldBZ.Group.GL.PadicBlocks` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviTopology` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfCharacter` |
| `Langlands.Representation.Induction.Parabolic` | `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf` | `Langlands.GeneralLinear.BlockShape.productInductionFunctorOf` |
| `Langlands.Representation.Filtration.ObjectDefinitions` | `Langlands.ObjectRepFiltration` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_comp_factorMap` |
| `Langlands.Representation.Jacquet.PositiveCharacter` | `Langlands.Jacquet.complexCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus` |
| `Langlands.AllFieldBZ.Representation.Induction.SingleBlock` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv` |
| `Langlands.Representation.Induction.HeterogeneousPairs` | `Representation.Equiv.precomp` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv` |
| `Langlands.Group.GL.AdjacentMergeShape` | `Langlands.GeneralLinear.BlockShape.index_index_eq_of_lex` | `Langlands.Parabolic.rightLabelEquiv_index` |
| `Langlands.Group.GL.OneBlockShape` | `Langlands.CuspidalSupport.LeviAdmissibility.oneBlock` | `Langlands.Parabolic.rightRefinement` |
| `Langlands.Representation.Geometric.WeylDefinitions` | `Langlands.Geometric.BlockRefinement` | `Langlands.Parabolic.rightRefinement` |
| `Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingStatement` | `Langlands.AllFieldBZ.Parabolic.OrderedProductRegrouping._proof_2` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.regroupingEquiv` |
| `Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingProof` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` | `_private.Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity.0.Langlands.Aubert.LocalFieldGraded.regroupingEquiv` |
| `Langlands.Representation.Smooth.Transfer.SubquotientProof` | `Langlands.isSmooth_of_surjective` | `Langlands.BinaryTensor.isSmooth_lift` |
| `Langlands.Representation.Smooth.SmoothPart.BasicProof` | `Langlands.isSmoothVector_add` | `Langlands.BinaryTensor.isSmooth_secondFactor` |
| `Langlands.Representation.Filtration.LengthTwoMatching` | `Langlands.LengthTwo.isIrreducible_of_equiv` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_irreducible` |
| `Langlands.Representation.Filtration.SmoothGradedObject` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.gradedSmooth` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_irreducible` |
| `Langlands.Representation.Filtration.Definitions` | `Langlands.RepFunctorFiltration` | `Langlands.ObjectRepFiltration` |
| `Langlands.Representation.Category.Subquotients` | `Langlands.SmoothRep.subrepresentation` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_seriesClass` |
| `Langlands.AllFieldBZ.Representation.Tensor.GLRefinement` | `Langlands.AllFieldBZ.FiniteTensor.rankCastLinearEquiv` | `Langlands.AllFieldBZ.FiniteTensor.rankCastRepresentationEquiv` |
| `Langlands.Representation.Induction.SingleBlock` | `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv` |
| `Langlands.Group.GL.TriangularParabolic` | `Langlands.GeneralLinear.BlockShape.index_lt_index_of_block_lt` | `Langlands.GeneralLinear.BlockShape.index_index_eq_of_lex` |
| `Langlands.Representation.Geometric.WeylUniquenessProof` | `Langlands.Geometric.blockIndex_monotone` | `Langlands.GeneralLinear.BlockShape.index_index_eq_of_lex` |
| `Langlands.Representation.Geometric.WeylMinimalRepresentativeProof` | `Langlands.Geometric.index_strictMono` | `Langlands.GeneralLinear.BlockShape.index_index_eq_of_lex` |
| `Langlands.AllFieldBZ.Representation.Parabolic.ComposedFunctors` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingRepresentation` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Group.GL.Padic` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearTopology` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedRefinedInductionFunctor` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementTransitivityStatement` | `Langlands.AllFieldBZ.Parabolic.NormalizedRefinementInductionTransitivityClause` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorStatement` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.BlockFunctions` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCoordinatesNormalizationStatement` | `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementInductionTransitivityProof` | `Langlands.AllFieldBZ.Parabolic.normalizedRefinementInductionTransitivity` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorProof` | `Langlands.AllFieldBZ.Parabolic.refinedInductionTensor` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCoordinatesNormalizationProof` | `Langlands.AllFieldBZ.Parabolic.refinementCoordinatesNormalization` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.Group.GL.RefinementCoordinates` | `Langlands.GeneralLinear.BlockShape.leviRefinementEquiv` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.Representation.Geometric.RefinementFunctors` | `Langlands.Geometric.refinedInducingRepresentation` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.Representation.Geometric.RefinementDefinitions` | `Langlands.Geometric.refinedLeviEquiv` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.Representation.Parabolic.RefinementComposition` | `Langlands.Parabolic.composedParabolic` | `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping` |
| `Langlands.Representation.Filtration.MultiplicityStatement` | `Langlands.HasJordanHolderMultiplicity` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_shortExact` |
| `Langlands.Representation.Filtration.MultiplicityIndependenceProof` | `Langlands.HasJordanHolderMultiplicity.unique` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_shortExact` |
| `Langlands.Representation.Filtration.MultiplicityAdditivityProof` | `Langlands.jordanHolderShortExactAdditivity` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_shortExact` |
| `Langlands.Representation.Filtration.LengthCriterionProof` | `Langlands.LengthCriterionProof.lower` | `Langlands.SmoothRep.IrreducibleGrothendieckProof.oneStep_graded_equiv` |
| `Langlands.AllFieldBZ.Group.GL.NormalizedCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantNorm` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm` |
| `Langlands.Representation.Tensor.FiniteEquivalences` | `Langlands.FiniteTensor.evalOne` | `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedParabolicHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingRepresentation` |
| `Langlands.Representation.Parabolic.RefinementPreimage` | `Langlands.Parabolic.leviPreimage` | `Langlands.Parabolic.composedParabolic` |
| `Langlands.Representation.Filtration.MultiplicityAdditivityStatement` | `Langlands.JordanHolderShortExactAdditivityStatement` | `Langlands.jordanHolderShortExactAdditivity` |
| `Langlands.Representation.Filtration.MultiplicityTransportProof` | `Langlands.equivJordanHolderMultiplicityTransport` | `Langlands.jordanHolderShortExactAdditivity` |
| `Langlands.Representation.Tensor.FiniteRegrouping` | `Langlands.FiniteTensor.regroupLinearEquiv` | `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv` |
| `Langlands.Representation.Jacquet.Coinvariants` | `Langlands.Jacquet.relations._proof_1` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedJacquet._proof_1` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorMap` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.comparison_of_pointwiseMap_bijective` |
| `Langlands.AllFieldBZ.Group.GL.CompactOpen` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearNonarchimedean` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorNormalization` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.blockInducingRepresentation` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof` | `Langlands.AllFieldBZ.Parabolic.parabolicQuotientCompact` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement` | `Langlands.Induction.FiniteProductTensorBijectiveTheorem._proof_1` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.Group.LeftQuotient` | `Langlands.Induction.LeftQuotient` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.Representation.Induction.FiniteProductTensor` | `Langlands.Induction.finiteProductTensorMap` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.Representation.Induction.FiniteProductTensorBijectiveProof` | `Langlands.Induction.finiteProductTensorMap_bijective` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` |
| `Langlands.Representation.Induction.ConjugateParabolic` | `Langlands.Induction.conjugateSmoothInducedEquiv` | `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.induction_of_halfModulus` |
| `Langlands.AllFieldBZ.Representation.Parabolic.FlattenedRefinementModulusCalculation` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus_flattened` | `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.modulus_of_coordinates` |
| `Langlands.Representation.CuspidalSupport.MinimalJacquetProof` | `Langlands.GeneralLinear.BlockShape.flatten` | `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.modulus_of_coordinates` |
| `Langlands.Representation.Geometric.FlattenedLevi` | `Langlands.Geometric.flattenedLeviEquiv` | `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.modulus_of_coordinates` |
| `Langlands.Representation.Filtration.JordanHolderComparisonProof` | `Langlands.jordanHolderSeriesComparison` | `Langlands.jordanHolderMultiplicityIndependence` |
| `Langlands.Representation.Filtration.MultiplicityTransportStatement` | `Langlands.EquivJordanHolderMultiplicityTransportStatement` | `Langlands.equivJordanHolderMultiplicityTransport` |
| `Langlands.Representation.Filtration.IntervalLiftStatement` | `Langlands.ActualQuotientSeriesLiftStatement.match_1` | `Langlands.jordanHolderFiltrationAdditivity` |
| `Langlands.Representation.Filtration.GradedRefinementProof` | `Langlands.GradedRefinementProof.assemble` | `Langlands.jordanHolderFiltrationAdditivity` |
| `Langlands.Representation.Filtration.IntervalLiftProof` | `Langlands.actualQuotientSeriesLift` | `Langlands.jordanHolderFiltrationAdditivity` |
| `Langlands.Group.GL.Nonarchimedean` | `Langlands.valuativeGeneralLinearNonarchimedean` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearNonarchimedean` |
| `Langlands.Representation.Induction.Equivalences` | `Langlands.Induction.smoothInducedEquiv` | `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducedNormalizationEquiv` |
| `Langlands.AllFieldBZ.Representation.Parabolic.GeometricPrerequisitesStatement` | `Langlands.AllFieldBZ.Parabolic.ParabolicQuotientCompactClause` | `Langlands.AllFieldBZ.Parabolic.parabolicQuotientCompact` |
| `Langlands.Representation.Whittaker.Iwasawa` | `Langlands.GeneralLinear.Iwasawa.integralRange` | `Langlands.AllFieldBZ.Parabolic.parabolicQuotientCompact` |
| `Langlands.Representation.Filtration.JordanHolderStatement` | `Langlands.JordanHolderSeriesComparisonStatement` | `Langlands.jordanHolderSeriesComparison` |
| `Langlands.Representation.Filtration.JordanHolderTransportProof` | `Langlands.jordanHolderSeriesTransport` | `Langlands.equivCompositionSeriesMultiplicityTransport` |
| `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof` | `Langlands.HarmonicAnalysis.GeneralLocalField.t2Space` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.fieldT2` |
| `Langlands.Group.GL.NonarchimedeanStatement` | `Langlands.ValuativeGeneralLinearNonarchimedean` | `Langlands.valuativeGeneralLinearNonarchimedean` |
| `Langlands.Representation.Conductor.Congruence` | `Langlands.Conductor.integralSubgroup` | `Langlands.AllFieldBZ.Parabolic.isCompact_integralRange` |
| `Langlands.Representation.Induction.CompactQuotientProof` | `Langlands.Induction.conjOpenSubgroup` | `Langlands.Induction.FiniteProductTensorBijective.finiteProductTensorMap_injective` |
| `Langlands.Representation.Tensor.FiniteProperties` | `Langlands.FiniteTensor.fixedVectors_external_le` | `Langlands.Induction.FiniteProductTensorBijective.finiteProductTensorMap_surjective` |
| `Langlands.LocalField.LocalFieldArithmetic` | `Langlands.LocalFieldData.normalizedAbs_le_iff_of_ne_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbs_eq_one_iff_discreteValuation` |
| `Langlands.LocalFactor.FML.Valuation` | `Langlands.FML.normalizedMultiplicativeValuation` | `Langlands.LocalFieldData.discreteValuation` |
| `Langlands.Topology.CompactOpen.NeighborhoodBasis` | `Langlands.compactOpenSubgroupBasis` | `Langlands.Induction.FiniteProductTensorBijective.exists_compact_level` |
| `Langlands.Representation.Induction.CompactLocalSection` | `Langlands.Induction.compactDoubleCosetSection` | `Langlands.Induction.FiniteProductTensorBijective.sectionMap` |
| `Langlands.Group.GL.RankMaps` | `Langlands.GeneralLinear.rankInclusion` | `Langlands.GeneralLinear.Iwasawa.exists_mul_upperTriangular._f` |
| `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` | `Langlands.CompactOpenSubgroupBasis` | `Langlands.compactOpenSubgroupBasis` |
| `Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation` | `Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding` | `_private.Langlands.AllFieldBZ.Representation.Parabolic.FlattenedRefinementModulusCalculation.0.Langlands.Parabolic.FlattenedModulusCalculation.determinantNorm_leviEmbedding` |
| `Langlands.Representation.Classification.SupercuspidalTwist` | `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantNorm_refinedUnipotent` |

## Declarations by defining module

Modules are in alphabetical order, and so are the declarations of each
module.

### `Langlands.AllFieldBZ.Group.GL.BlockModulus` (17)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leviHalfModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leviModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_normOneLevi`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_eq_one`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_eq_one._simp_1_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_apply`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.mem_normOneLevi`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.mem_normOneLevi._simp_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normOneLevi`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normOneLevi_le_ker_leviModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicModulus._proof_1`, theorem

### `Langlands.AllFieldBZ.Group.GL.CompactOpen` (1)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearNonarchimedean`, theorem

### `Langlands.AllFieldBZ.Group.GL.NormalizedCharacter` (14)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantNorm`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_determinantNorm`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_normalizedAbsUnits`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_normalizedAbsUnits._simp_1_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_4`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_5`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_6`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsHom._proof_7`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsUnits`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbs_eq_one_iff_discreteValuation`, theorem

### `Langlands.AllFieldBZ.Group.GL.Padic` (6)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearDeterminant`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearDeterminant._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearLocallyCompactSpace`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearLocallyCompactSpace._proof_1_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearTopologicalGroup`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.generalLinearTopology`, definition

### `Langlands.AllFieldBZ.Group.GL.PadicBlocks` (2)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviTopologicalGroup`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviTopology`, definition

### `Langlands.AllFieldBZ.LocalField.Definitions` (7)

- `Langlands.AllFieldBZ.LocalFieldPackage`, inductive type
- `Langlands.AllFieldBZ.LocalFieldPackage.Carrier`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.fieldT2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.field`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.mk`, constructor
- `Langlands.AllFieldBZ.LocalFieldPackage.ofField`, definition

### `Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions` (9)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviBlock`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviBlock._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviBlock._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviModulus._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviModulus_apply`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus_apply`, theorem

### `Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors` (4)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedRefinedInduced`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedRefinedInduced._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedRefinedInduced._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedRefinedInductionFunctor`, definition

### `Langlands.AllFieldBZ.Representation.Induction.BinaryProduct` (30)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorObj`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorObj._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor.eq_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_left_eq_zero`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_pos`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_right_eq_zero`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductLeftZeroIso`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductPositiveIso`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductRightZeroIso`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPairFamilyFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPairFamilyFunctor._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorObj`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorObj._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv._proof_4`, theorem

### `Langlands.AllFieldBZ.Representation.Induction.BlockEquivalence` (2)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInducedEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInducedEquiv._proof_1`, theorem

### `Langlands.AllFieldBZ.Representation.Induction.BlockFactors` (3)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInduced`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInductionFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isTopologicalRing` (private), theorem

### `Langlands.AllFieldBZ.Representation.Induction.Parabolic` (4)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfCharacter`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedParabolicInduced`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedParabolicInductionFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isTopologicalRing` (private), theorem

### `Langlands.AllFieldBZ.Representation.Induction.SingleBlock` (14)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_4`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_5`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedInducedEquiv._proof_6`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockNormalizedProductEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlock_leviHalfModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlock_leviModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlock_parabolicHalfModulus`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.ComposedFunctors` (15)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingMap`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingMap._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingMap._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingMap._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingMap._proof_4`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingRepresentation`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedInducingRepresentation._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isSmooth_normalizedComposedInduced`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInduced`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInducedMap`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInductionFunctor`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInductionFunctor._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInductionFunctor._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedInductionFunctor._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedComposedJacquet._proof_1`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.FlattenedRefinementModulusCalculation` (13)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus_flattened`, theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.determinantNorm_flattenedComponent` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.determinantNorm_leviEmbedding` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.determinantNorm_sizeTransport` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.differentOuterProduct` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.flattenProduct` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.fullModulus` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.innerBlock` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.lexFactor` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.lexProduct` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.outerDeterminantNorm` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.rectangularProduct` (private), theorem
- `Langlands.Parabolic.FlattenedModulusCalculation.sameOuterProduct` (private), theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.GeometricPrerequisitesStatement` (1)

- `Langlands.AllFieldBZ.Parabolic.ParabolicQuotientCompactClause`, definition

### `Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingProof` (1)

- `Langlands.AllFieldBZ.Parabolic.orderedProductRegrouping`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingStatement` (3)

- `Langlands.AllFieldBZ.Parabolic.OrderedProductRegrouping`, definition
- `Langlands.AllFieldBZ.Parabolic.OrderedProductRegrouping._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.OrderedProductRegrouping._proof_2`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof` (3)

- `Langlands.AllFieldBZ.Parabolic.isCompact_integralRange`, theorem
- `Langlands.AllFieldBZ.Parabolic.parabolicQuotientCompact`, theorem
- `Langlands.AllFieldBZ.Parabolic.quotientMap_image_integralRange`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorMap` (16)

- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducedNormalizationEquiv`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducedNormalizationEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_4`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_5`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv._proof_6`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap._proof_2`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap._proof_3`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap._proof_4`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_tprod_eval`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.productInducing_eq`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorNormalization` (8)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviBlock_projection`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus_eq_prod`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus_eq_prod`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.blockInducingRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.coordinateInducingRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.coordinateInducingRepresentation_eq`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.normalizedRefinedInducingRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.normalizedRefinedInducingRepresentation._proof_1`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorProof` (3)

- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.comparison_of_pointwiseMap_bijective`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.pointwiseMap_bijective`, theorem
- `Langlands.AllFieldBZ.Parabolic.refinedInductionTensor`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinedInductionTensorStatement` (13)

- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.BlockFunctions`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.CanonicalInverse`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.CanonicalInverse._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Comparison`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.RefinedFunctions`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.blockRepresentations`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.inducingRepresentation._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.refinedRepresentation`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinedInductionTensorTheorem`, definition

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCharacter` (7)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantNorm_refinedUnipotent`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_refinedUnipotent`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterModulus._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedUnipotent_le_ker_leviModulus`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedUnipotent_le_normOneLevi`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition` (9)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviHalfModulus_eq`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedLeviModulus._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedParabolicHalfModulus`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.composedParabolicHalfModulus._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterHalfModulus_projection`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedOuterModulus_projection`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCoordinatesNormalizationProof` (6)

- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.halfModulus_of_modulus`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.induction_of_halfModulus`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.modulus_of_coordinates`, theorem
- `Langlands.AllFieldBZ.Parabolic.refinementCoordinatesNormalization`, theorem
- `Langlands.Parabolic.RefinementCoordinatesNormalization.block_cast_eq` (private), theorem
- `Langlands.Parabolic.RefinementCoordinatesNormalization.shape_eq_flatten` (private), theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementCoordinatesNormalizationStatement` (9)

- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause._proof_2`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.InductionClause`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.InductionClause._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.InductionClause._proof_2`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.ModulusClause`, definition
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalization.ModulusClause._proof_1`, theorem
- `Langlands.AllFieldBZ.Parabolic.RefinementCoordinatesNormalizationTheorem`, definition

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementInductionTransitivityProof` (41)

- `Langlands.AllFieldBZ.Parabolic.normalizedRefinementInductionTransitivity`, theorem
- `Langlands.Parabolic.Direct` (private), definition
- `Langlands.Parabolic.Inner` (private), definition
- `Langlands.Parabolic.Inner._proof_1` (private), theorem
- `Langlands.Parabolic.Iterated` (private), definition
- `Langlands.Parabolic.Iterated._proof_1` (private), theorem
- `Langlands.Parabolic.composed_half` (private), theorem
- `Langlands.Parabolic.direct_cov` (private), theorem
- `Langlands.Parabolic.direct_outer` (private), theorem
- `Langlands.Parabolic.direct_section` (private), theorem
- `Langlands.Parabolic.forward` (private), definition
- `Langlands.Parabolic.forward._proof_1` (private), theorem
- `Langlands.Parabolic.forward._proof_2` (private), theorem
- `Langlands.Parabolic.forward._proof_3` (private), theorem
- `Langlands.Parabolic.forward._proof_4` (private), theorem
- `Langlands.Parabolic.forward._proof_5` (private), theorem
- `Langlands.Parabolic.forward_eval` (private), theorem
- `Langlands.Parabolic.forward_inverse` (private), theorem
- `Langlands.Parabolic.inverse` (private), definition
- `Langlands.Parabolic.inverse._proof_1` (private), theorem
- `Langlands.Parabolic.inverse._proof_2` (private), theorem
- `Langlands.Parabolic.inverse._proof_3` (private), theorem
- `Langlands.Parabolic.inverse._proof_4` (private), theorem
- `Langlands.Parabolic.inverseInner` (private), definition
- `Langlands.Parabolic.inverseInner._proof_1` (private), theorem
- `Langlands.Parabolic.inverseValue` (private), definition
- `Langlands.Parabolic.inverseValue_cov` (private), theorem
- `Langlands.Parabolic.inverseValue_outer` (private), theorem
- `Langlands.Parabolic.inverseValue_smooth` (private), theorem
- `Langlands.Parabolic.inverse_eval` (private), theorem
- `Langlands.Parabolic.inverse_forward` (private), theorem
- `Langlands.Parabolic.iterated_cov` (private), theorem
- `Langlands.Parabolic.transitivityEquiv` (private), definition
- `Langlands.Parabolic.transitivityEquiv._proof_1` (private), theorem
- `Langlands.Parabolic.transitivityEquiv._proof_2` (private), theorem
- `Langlands.Parabolic.transitivityEquiv._proof_3` (private), theorem
- `Langlands.Parabolic.transitivityEquiv._proof_4` (private), theorem
- `Langlands.Parabolic.transitivityEquiv._proof_5` (private), theorem
- `Langlands.Parabolic.transitivityEquiv._proof_6` (private), theorem
- `Langlands.Parabolic.transitivityIso` (private), definition
- `Langlands.Parabolic.transitivityIso._proof_1` (private), theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.RefinementTransitivityStatement` (1)

- `Langlands.AllFieldBZ.Parabolic.NormalizedRefinementInductionTransitivityClause`, definition

### `Langlands.AllFieldBZ.Representation.Parabolic.RegroupingFactorEquivalences` (12)

- `Langlands.AllFieldBZ.FiniteTensor.rankCastRepresentationEquiv`, definition
- `Langlands.AllFieldBZ.FiniteTensor.rankCastRepresentationEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.rankCastRepresentationEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.rankCastRepresentationEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv`, definition
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_4`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_5`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_6`, theorem
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.singleBlockTransportedProductEquiv._proof_7`, theorem

### `Langlands.AllFieldBZ.Representation.Parabolic.ThreeBlockRegroupingAssembly` (1)

- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInductionObjEquiv`, definition

### `Langlands.AllFieldBZ.Representation.Tensor.GLRefinement` (17)

- `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv`, definition
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv`, definition
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_3`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_4`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_5`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_6`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv._proof_7`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.glRefinementLinearEquiv_tprod`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.rankCastLinearEquiv`, definition
- `Langlands.AllFieldBZ.FiniteTensor.rankCastLinearEquiv._proof_1`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.rankCastLinearEquiv._proof_2`, theorem
- `Langlands.AllFieldBZ.FiniteTensor.rankCastLinearEquiv_action`, theorem

### `Langlands.Group.GL.AdjacentMergeShape` (1)

- `Langlands.GeneralLinear.BlockShape.index_index_eq_of_lex`, theorem

### `Langlands.Group.GL.Basic` (8)

- `Langlands.GeneralLinear`, definition
- `Langlands.GeneralLinear.determinant`, definition
- `Langlands.GeneralLinear.determinantContinuous`, definition
- `Langlands.GeneralLinear.determinantContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.reindex`, definition
- `Langlands.GeneralLinear.reindexContinuous`, definition
- `Langlands.GeneralLinear.reindexContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.reindexContinuous._proof_2`, theorem

### `Langlands.Group.GL.Blocks` (84)

- `Langlands.GeneralLinear.BlockShape`, inductive type
- `Langlands.GeneralLinear.BlockShape.Index`, definition
- `Langlands.GeneralLinear.BlockShape.Levi`, definition
- `Langlands.GeneralLinear.BlockShape.casesOn`, definition
- `Langlands.GeneralLinear.BlockShape.diagonalBlock`, definition
- `Langlands.GeneralLinear.BlockShape.index`, definition
- `Langlands.GeneralLinear.BlockShape.index._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.indexEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.length`, definition
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic`, definition
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.leviAsParabolic._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEmbedding`, definition
- `Langlands.GeneralLinear.BlockShape.leviEmbeddingContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.leviEmbeddingContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEmbedding_apply_same`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.leviEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquiv._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquiv._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquiv._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquivContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.leviEquivContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviEquivContinuous._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.leviInParabolic`, definition
- `Langlands.GeneralLinear.BlockShape.leviProjection`, definition
- `Langlands.GeneralLinear.BlockShape.leviProjection._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviProjectionContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.leviProjectionContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.leviProjection_apply`, theorem
- `Langlands.GeneralLinear.BlockShape.leviProjection_section`, theorem
- `Langlands.GeneralLinear.BlockShape.leviSubgroup`, definition
- `Langlands.GeneralLinear.BlockShape.mem_parabolic_iff`, theorem
- `Langlands.GeneralLinear.BlockShape.mem_unipotentRadical_iff`, theorem
- `Langlands.GeneralLinear.BlockShape.mem_unipotentSubgroup_iff`, theorem
- `Langlands.GeneralLinear.BlockShape.mk`, constructor
- `Langlands.GeneralLinear.BlockShape.parabolic`, definition
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates`, definition
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_6`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_7`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinates._proof_8`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinatesContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinatesContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicCoordinatesContinuous._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.positive`, theorem
- `Langlands.GeneralLinear.BlockShape.rec`, recursor
- `Langlands.GeneralLinear.BlockShape.sigmaLeviEmbedding`, definition
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection`, definition
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_6`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_7`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_8`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection._proof_9`, theorem
- `Langlands.GeneralLinear.BlockShape.sigmaParabolic`, definition
- `Langlands.GeneralLinear.BlockShape.size`, definition
- `Langlands.GeneralLinear.BlockShape.sum_eq`, theorem
- `Langlands.GeneralLinear.BlockShape.unipotentPart`, definition
- `Langlands.GeneralLinear.BlockShape.unipotentPart._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.unipotentRadical`, definition
- `Langlands.GeneralLinear.BlockShape.unipotentSubgroup`, definition
- `Langlands.GeneralLinear.BlockShape.continuous_sigmaLeviEmbedding` (private), theorem
- `Langlands.GeneralLinear.BlockShape.continuous_sigmaLeviProjection` (private), theorem
- `Langlands.GeneralLinear.BlockShape.diagonalBlock_mul` (private), theorem
- `Langlands.GeneralLinear.BlockShape.diagonalBlock_one` (private), theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviInParabolic` (private), definition
- `Langlands.GeneralLinear.BlockShape.sigmaLeviInParabolic._proof_1` (private), theorem
- `Langlands.GeneralLinear.BlockShape.sigmaLeviProjection_section` (private), theorem
- `Langlands.GeneralLinear.BlockShape.triangularSubgroup` (private), definition
- `Langlands.GeneralLinear.BlockShape.triangularSubgroup._proof_1` (private), theorem
- `Langlands.GeneralLinear.BlockShape.triangularSubgroup._proof_2` (private), theorem
- `Langlands.GeneralLinear.BlockShape.triangularSubgroup._proof_3` (private), theorem

### `Langlands.Group.GL.MirabolicOppositeIntersection` (3)

- `Langlands.GeneralLinear.BlockShape.binary`, definition
- `Langlands.GeneralLinear.BlockShape.binary._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.binary._proof_2`, theorem

### `Langlands.Group.GL.Nonarchimedean` (10)

- `Langlands.valuativeGeneralLinearNonarchimedean`, theorem
- `Langlands.existsSmallMatrix` (private), theorem
- `Langlands.finitePiBasis` (private), theorem
- `Langlands.matrixZeroBasis` (private), theorem
- `Langlands.valuativeBallOpen` (private), theorem
- `Langlands.valuativeMatrixMonoid` (private), definition
- `Langlands.valuativeMatrixMonoid._abel_1` (private), theorem
- `Langlands.valuativeMatrixMonoid._proof_1` (private), theorem
- `Langlands.valuativeMatrixMonoid._proof_2` (private), theorem
- `Langlands.valuativeMatrixMonoidOpen` (private), theorem

### `Langlands.Group.GL.NonarchimedeanStatement` (1)

- `Langlands.ValuativeGeneralLinearNonarchimedean`, definition

### `Langlands.Group.GL.OneBlockShape` (2)

- `Langlands.CuspidalSupport.LeviAdmissibility.oneBlock`, definition
- `Langlands.CuspidalSupport.LeviAdmissibility.oneBlock._proof_1`, theorem

### `Langlands.Group.GL.RankMaps` (17)

- `Langlands.GeneralLinear.blockSum`, definition
- `Langlands.GeneralLinear.blockSum_apply_left`, theorem
- `Langlands.GeneralLinear.blockSum_apply_left_right`, theorem
- `Langlands.GeneralLinear.blockSum_apply_right`, theorem
- `Langlands.GeneralLinear.blockSum_apply_right_left`, theorem
- `Langlands.GeneralLinear.rankInclusion`, definition
- `Langlands.GeneralLinear.rankInclusion._proof_1`, theorem
- `Langlands.GeneralLinear.rankInclusion._proof_2`, theorem
- `Langlands.GeneralLinear.blockSumCoordinates` (private), definition
- `Langlands.GeneralLinear.blockSumCoordinates._proof_1` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_2` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_3` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_4` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_5` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_6` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_7` (private), theorem
- `Langlands.GeneralLinear.blockSumCoordinates._proof_8` (private), theorem

### `Langlands.Group.GL.RankReindex` (2)

- `Langlands.GeneralLinear.continuous_reindex_finCongr`, theorem
- `Langlands.GeneralLinear.reindex_finCongr_rfl`, theorem

### `Langlands.Group.GL.RefinementCoordinates` (25)

- `Langlands.GeneralLinear.BlockShape.composedLeviProjection_parabolicRefinementEquiv`, theorem
- `Langlands.GeneralLinear.BlockShape.composedParabolic_eq_of_coordinates`, theorem
- `Langlands.GeneralLinear.BlockShape.leviRefinementEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.leviRefinementEquivContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquivContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquivContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquivContinuous._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv_apply`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv_entry`, theorem
- `Langlands.GeneralLinear.BlockShape.nestedLeviEquiv_symm_apply`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_6`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_7`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_8`, theorem
- `Langlands.GeneralLinear.BlockShape.parabolicRefinementEquiv._proof_9`, theorem
- `Langlands.GeneralLinear.BlockShape.refinementBlock_lt_of_outer_lt`, theorem
- `Langlands.GeneralLinear.BlockShape.refinementBlock_strictMono`, theorem

### `Langlands.Group.GL.SingleBlock` (19)

- `Langlands.GeneralLinear.BlockShape.eq_singleBlockIndex`, theorem
- `Langlands.GeneralLinear.BlockShape.eq_singleBlockIndex._proof_1_2`, theorem
- `Langlands.GeneralLinear.BlockShape.rankCast`, definition
- `Langlands.GeneralLinear.BlockShape.rankCast._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockIndex`, definition
- `Langlands.GeneralLinear.BlockShape.singleBlockIndex._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockIndex._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquivContinuous`, definition
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquivContinuous._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquivContinuous._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlock_index_val`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlock_leviEmbedding_projection`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlock_parabolic_eq_top`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlock_size`, theorem

### `Langlands.Group.GL.TriangularParabolic` (3)

- `Langlands.GeneralLinear.BlockShape.index_lt_index_of_block_lt`, theorem
- `Langlands.GeneralLinear.BlockShape.index_lt_index_of_block_lt._proof_1_2`, theorem
- `Langlands.GeneralLinear.BlockShape.mem_parabolic_of_isUpperTriangular`, theorem

### `Langlands.Group.LeftQuotient` (2)

- `Langlands.Induction.LeftQuotient`, definition
- `Langlands.Induction.quotientMap`, definition

### `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof` (2)

- `Langlands.HarmonicAnalysis.GeneralLocalField.properNormedField`, theorem
- `Langlands.HarmonicAnalysis.GeneralLocalField.t2Space`, theorem

### `Langlands.LocalFactor.FML.Valuation` (3)

- `Langlands.FML.normalizedMultiplicativeValuation`, definition
- `Langlands.FML.normalizedMultiplicativeValuation._proof_1`, theorem
- `Langlands.FML.normalizedMultiplicativeValuation._proof_2`, theorem

### `Langlands.LocalField.LocalFieldArithmetic` (12)

- `Langlands.LocalFieldData.finite_residueField`, theorem
- `Langlands.LocalFieldData.finite_residueField._proof_1_1`, theorem
- `Langlands.LocalFieldData.normalizedAbs_le_iff_of_ne_zero`, theorem
- `Langlands.LocalFieldData.normalizedAbs_mul`, theorem
- `Langlands.LocalFieldData.normalizedAbs_nonneg`, theorem
- `Langlands.LocalFieldData.normalizedAbs_of_ne_zero`, theorem
- `Langlands.LocalFieldData.normalizedAbs_one`, theorem
- `Langlands.LocalFieldData.normalizedAbs_pos`, theorem
- `Langlands.LocalFieldData.normalizedAbs_zero`, theorem
- `Langlands.LocalFieldData.ord_mul`, theorem
- `Langlands.LocalFieldData.ord_one`, theorem
- `Langlands.LocalFieldData.residueCardinality_gt_one`, theorem

### `Langlands.LocalField.LocalFieldData` (13)

- `Langlands.LocalFieldData`, inductive type
- `Langlands.LocalFieldData.Integers`, definition
- `Langlands.LocalFieldData.ResidueField`, definition
- `Langlands.LocalFieldData.ResidueField._proof_1`, theorem
- `Langlands.LocalFieldData.discreteValuation`, definition
- `Langlands.LocalFieldData.localField`, theorem
- `Langlands.LocalFieldData.mk`, constructor
- `Langlands.LocalFieldData.normalizedAbs`, definition
- `Langlands.LocalFieldData.ord`, definition
- `Langlands.LocalFieldData.ord._proof_1`, theorem
- `Langlands.LocalFieldData.residueCardinality`, definition
- `Langlands.LocalFieldData.topology`, definition
- `Langlands.LocalFieldData.valuativeRel`, definition

### `Langlands.Representation.Aubert.LocalFieldBinaryProductExactLengthStatement` (1)

- `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement`, definition

### `Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitProof` (7)

- `Langlands.Aubert.LocalFieldGraded.inclusion_zero_eq_smul`, theorem
- `Langlands.Aubert.LocalFieldGraded.localFieldGradedAssociativeUnit`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication_assoc`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation.eq_1`, theorem
- `Langlands.Aubert.LocalFieldGraded.assoc_on_objects` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.graded_ext_objects` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.rankZero_equiv_unit` (private), theorem

### `Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitStatement` (2)

- `Langlands.Aubert.LocalFieldGraded.LocalFieldGradedAssociativeUnitStatement`, definition
- `Langlands.Aubert.LocalFieldGraded.LocalFieldGradedAssociativeUnitStatement._proof_1`, theorem

### `Langlands.Representation.Aubert.LocalFieldGradedGrothendieck` (20)

- `Langlands.Aubert.LocalFieldGraded.GradedGrothendieckGroup`, definition
- `Langlands.Aubert.LocalFieldGraded.binaryProduct`, definition
- `Langlands.Aubert.LocalFieldGraded.binaryProduct._proof_1`, theorem
- `Langlands.Aubert.LocalFieldGraded.binaryProduct._proof_2`, theorem
- `Langlands.Aubert.LocalFieldGraded.binaryProduct._proof_3`, theorem
- `Langlands.Aubert.LocalFieldGraded.binaryProduct._proof_4`, theorem
- `Langlands.Aubert.LocalFieldGraded.binaryProduct_objects`, theorem
- `Langlands.Aubert.LocalFieldGraded.inclusion`, definition
- `Langlands.Aubert.LocalFieldGraded.multiplication`, definition
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_1`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_2`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_3`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_4`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_5`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication._proof_6`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication_homogeneous`, theorem
- `Langlands.Aubert.LocalFieldGraded.unit`, definition
- `Langlands.Aubert.LocalFieldGraded.unitObject`, definition
- `Langlands.Aubert.LocalFieldGraded.unitObject._proof_1`, theorem
- `Langlands.Aubert.LocalFieldGraded.unitObject_hasFiniteLength`, theorem

### `Langlands.Representation.Aubert.LocalFieldGradedInductionUnit` (5)

- `Langlands.Aubert.LocalFieldGraded.inclusion_eq_of_rank_equiv`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication_unit_left`, theorem
- `Langlands.Aubert.LocalFieldGraded.multiplication_unit_right`, theorem
- `Langlands.Aubert.LocalFieldGraded.leftUnit_object` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.rightUnit_object` (private), theorem

### `Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity` (39)

- `Langlands.Aubert.LocalFieldGraded.inducedRankCast`, definition
- `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv`, definition
- `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv._proof_1`, theorem
- `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv._proof_2`, theorem
- `Langlands.Aubert.LocalFieldGraded.positiveAssociativityEquiv._proof_3`, theorem
- `Langlands.Aubert.LocalFieldGraded.productShape_eq`, theorem
- `Langlands.Aubert.LocalFieldGraded.pairFamilyEquiv` (private), definition
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv` (private), definition
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv._proof_1` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv._proof_2` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv._proof_3` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv._proof_4` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.pairProductEquiv.match_1` (private), definition
- `Langlands.Aubert.LocalFieldGraded.productFamilyEquiv` (private), definition
- `Langlands.Aubert.LocalFieldGraded.productFamilyEquiv._proof_1` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair` (private), definition
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_1` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_2` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_3` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_4` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_5` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_6` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_7` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair._proof_8` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupLeftPair.match_1` (private), definition
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair` (private), definition
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_1` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_2` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_3` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_4` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_5` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_6` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_7` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair._proof_8` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupRightPair.match_1` (private), definition
- `Langlands.Aubert.LocalFieldGraded.regroupingEquiv` (private), definition
- `Langlands.Aubert.LocalFieldGraded.regroupingEquiv._proof_1` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupingEquiv._proof_2` (private), theorem
- `Langlands.Aubert.LocalFieldGraded.regroupingEquiv._proof_3` (private), theorem

### `Langlands.Representation.Category.Basic` (14)

- `Langlands.SmoothRep`, definition
- `Langlands.SmoothRep.HasFiniteLength`, definition
- `Langlands.SmoothRep.IsIrreducible`, definition
- `Langlands.SmoothRep.equivOfIso`, definition
- `Langlands.SmoothRep.hom`, definition
- `Langlands.SmoothRep.instAddCommGroupVObjRepSmoothRepProperty`, definition
- `Langlands.SmoothRep.instModuleVObjRepSmoothRepProperty`, definition
- `Langlands.SmoothRep.isSmooth`, theorem
- `Langlands.SmoothRep.mkIso`, definition
- `Langlands.SmoothRep.of`, definition
- `Langlands.SmoothRep.ofHom`, definition
- `Langlands.SmoothRep.representation`, definition
- `Langlands.SmoothRep.toRep`, definition
- `Langlands.smoothRepProperty`, definition

### `Langlands.Representation.Category.Subquotients` (5)

- `Langlands.SmoothRep.stable`, theorem
- `Langlands.SmoothRep.subrepresentation`, definition
- `Langlands.SmoothRep.subrepresentation._proof_1`, theorem
- `Langlands.SmoothRep.subtype`, definition
- `Langlands.SmoothRep.subtype_injective`, theorem

### `Langlands.Representation.Classification.SupercuspidalTwist` (1)

- `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup`, theorem

### `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge` (1)

- `Langlands.Classification.BinaryProductBridge.binary_eq_twoBlocks`, theorem

### `Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement` (1)

- `Langlands.Classification.twoBlockFactors`, definition

### `Langlands.Representation.Conductor.Congruence` (35)

- `Langlands.Conductor.congruenceSubgroup`, definition
- `Langlands.Conductor.congruenceSubgroup._proof_1`, theorem
- `Langlands.Conductor.congruenceSubgroup_top`, theorem
- `Langlands.Conductor.integralCongruence`, definition
- `Langlands.Conductor.integralCongruence_top`, theorem
- `Langlands.Conductor.integralCongruence_top._simp_1_1`, theorem
- `Langlands.Conductor.integralSubgroup`, definition
- `Langlands.Conductor.isCompact_congruenceSubgroup`, theorem
- `Langlands.Conductor.isCompact_congruenceSubgroup._proof_1_1`, theorem
- `Langlands.Conductor.isCompact_levelOpenSubgroup`, theorem
- `Langlands.Conductor.isOpenEmbedding_integral_map`, theorem
- `Langlands.Conductor.isOpen_congruenceSubgroup`, theorem
- `Langlands.Conductor.isOpen_integralCongruence`, theorem
- `Langlands.Conductor.isOpen_integralCongruence._simp_1_1`, theorem
- `Langlands.Conductor.isOpen_integralCongruence._simp_1_2`, theorem
- `Langlands.Conductor.isOpen_integralCongruence._simp_1_3`, theorem
- `Langlands.Conductor.isOpen_integralSubgroup`, theorem
- `Langlands.Conductor.isOpen_integralSubgroup._simp_1_1`, theorem
- `Langlands.Conductor.isOpen_integralSubgroup._simp_1_2`, theorem
- `Langlands.Conductor.isOpen_integralSubgroup._simp_1_3`, theorem
- `Langlands.Conductor.isOpen_integralSubgroup._simp_1_4`, theorem
- `Langlands.Conductor.levelOpenSubgroup`, definition
- `Langlands.Conductor.levelOpenSubgroup._proof_1`, theorem
- `Langlands.Conductor.levelSubgroup`, definition
- `Langlands.Conductor.levelSubgroup._proof_1`, theorem
- `Langlands.Conductor.levelSubgroup._proof_2`, theorem
- `Langlands.Conductor.levelSubgroup._proof_3`, theorem
- `Langlands.Conductor.levelSubgroup_zero`, theorem
- `Langlands.Conductor.mem_integralCongruence`, theorem
- `Langlands.Conductor.mem_integralSubgroup`, theorem
- `Langlands.Conductor.rowStabilizer`, definition
- `Langlands.Conductor.rowStabilizer._proof_1`, theorem
- `Langlands.Conductor.rowStabilizer._proof_2`, theorem
- `Langlands.Conductor.rowStabilizer._proof_3`, theorem
- `Langlands.Conductor.localField_t2` (private), theorem

### `Langlands.Representation.CuspidalSupport.MinimalJacquetProof` (13)

- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_iff`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of._proof_1_1`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of._proof_1_2`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of._proof_1_3`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of._proof_1_4`, theorem
- `Langlands.GeneralLinear.BlockShape.finSigmaFinEquiv_lt_of._proof_1_5`, theorem
- `Langlands.GeneralLinear.BlockShape.flatten`, definition
- `Langlands.GeneralLinear.BlockShape.flatten._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.flatten._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.flattenBlockEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.flattenBlockEquiv_lt_iff`, theorem
- `Langlands.GeneralLinear.BlockShape.flatten_size_flattenBlockEquiv`, theorem

### `Langlands.Representation.Derivative.ProductDerivativesFiniteLength` (1)

- `Langlands.Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_finiteDimensional`, theorem

### `Langlands.Representation.Filtration.Definitions` (38)

- `Langlands.RepFunctorFiltration`, inductive type
- `Langlands.RepFunctorFiltration.graded`, definition
- `Langlands.RepFunctorFiltration.mk`, constructor
- `Langlands.RepFunctorFiltration.monotone`, theorem
- `Langlands.RepFunctorFiltration.step`, definition
- `Langlands.RepFunctorFiltration.top`, theorem
- `Langlands.RepFunctorFiltration.zero`, theorem
- `Langlands.RepSubfunctor`, inductive type
- `Langlands.RepSubfunctor.lowerInUpper`, definition
- `Langlands.RepSubfunctor.lowerInUpper._proof_1`, theorem
- `Langlands.RepSubfunctor.map`, definition
- `Langlands.RepSubfunctor.map._proof_1`, theorem
- `Langlands.RepSubfunctor.map._proof_2`, theorem
- `Langlands.RepSubfunctor.map._proof_3`, theorem
- `Langlands.RepSubfunctor.map._proof_4`, theorem
- `Langlands.RepSubfunctor.map._proof_5`, theorem
- `Langlands.RepSubfunctor.map._proof_6`, theorem
- `Langlands.RepSubfunctor.map._proof_7`, theorem
- `Langlands.RepSubfunctor.map_mem`, theorem
- `Langlands.RepSubfunctor.mk`, constructor
- `Langlands.RepSubfunctor.obj`, definition
- `Langlands.RepSubfunctor.quotientFunctor`, definition
- `Langlands.RepSubfunctor.quotientFunctor._proof_1`, theorem
- `Langlands.RepSubfunctor.quotientFunctor._proof_2`, theorem
- `Langlands.RepSubfunctor.quotientMap`, definition
- `Langlands.RepSubfunctor.quotientMap._proof_1`, theorem
- `Langlands.RepSubfunctor.quotientMap._proof_2`, theorem
- `Langlands.RepSubfunctor.quotientMap._proof_3`, theorem
- `Langlands.RepSubfunctor.quotientNatProjection`, definition
- `Langlands.RepSubfunctor.quotientNatProjection._proof_1`, theorem
- `Langlands.RepSubfunctor.quotientObj`, definition
- `Langlands.RepSubfunctor.quotientObj._proof_1`, theorem
- `Langlands.RepSubfunctor.quotientProjection`, definition
- `Langlands.RepSubfunctor.quotientProjection_surjective`, theorem
- `Langlands.RepSubfunctor.representation`, definition
- `Langlands.RepSubfunctor.toFunctor`, definition
- `Langlands.RepSubfunctor.toFunctor._proof_1`, theorem
- `Langlands.RepSubfunctor.toFunctor._proof_2`, theorem

### `Langlands.Representation.Filtration.GradedRefinementProof` (7)

- `Langlands.GradedRefinementProof.assemble`, theorem
- `Langlands.GradedRefinementProof.assemble.match_1`, definition
- `Langlands.GradedRefinementProof.concatenate`, theorem
- `Langlands.GradedRefinementProof.sigmaFinSucc`, definition
- `Langlands.GradedRefinementProof.sigmaFinSucc._proof_1`, theorem
- `Langlands.GradedRefinementProof.sigmaFinSucc._proof_2`, theorem
- `Langlands.GradedRefinementProof.sigmaFinSucc._proof_3`, theorem

### `Langlands.Representation.Filtration.IntervalLiftProof` (8)

- `Langlands.IntervalLiftProof.mem_pull_iff`, theorem
- `Langlands.IntervalLiftProof.nonempty_quotient_pull_equiv`, theorem
- `Langlands.IntervalLiftProof.pull_bot`, theorem
- `Langlands.IntervalLiftProof.pull_le`, theorem
- `Langlands.IntervalLiftProof.pull_mono`, theorem
- `Langlands.IntervalLiftProof.pull_top`, theorem
- `Langlands.actualQuotientSeriesLift`, theorem
- `Langlands.actualQuotientSeriesLift.match_1_1`, definition

### `Langlands.Representation.Filtration.IntervalLiftStatement` (2)

- `Langlands.ActualQuotientSeriesLiftStatement`, definition
- `Langlands.ActualQuotientSeriesLiftStatement.match_1`, definition

### `Langlands.Representation.Filtration.JordanHolderComparisonProof` (8)

- `Langlands.JordanHolderProof.quotientEquiv_of_intervalIso`, theorem
- `Langlands.JordanHolderProof.quotientEquiv_of_intervalIso.match_1_1`, definition
- `Langlands.JordanHolderProof.quotientSecondIso`, definition
- `Langlands.JordanHolderProof.quotientSecondIso._proof_1`, theorem
- `Langlands.JordanHolderProof.quotientSecondIso._proof_2`, theorem
- `Langlands.JordanHolderProof.quotientSecondIso._proof_3`, theorem
- `Langlands.JordanHolderProof.subrepresentationIsModularLattice`, theorem
- `Langlands.jordanHolderSeriesComparison`, theorem

### `Langlands.Representation.Filtration.JordanHolderStatement` (2)

- `Langlands.JordanHolderSeriesComparisonStatement`, definition
- `Langlands.JordanHolderSeriesTransportStatement`, definition

### `Langlands.Representation.Filtration.JordanHolderTransportProof` (16)

- `Langlands.JordanHolderTransportProof.equiv_apply_rep`, theorem
- `Langlands.JordanHolderTransportProof.mapSub`, definition
- `Langlands.JordanHolderTransportProof.mapSub._proof_1`, theorem
- `Langlands.JordanHolderTransportProof.mapSub._proof_2`, theorem
- `Langlands.JordanHolderTransportProof.mapSub._proof_3`, theorem
- `Langlands.JordanHolderTransportProof.map_lower`, theorem
- `Langlands.JordanHolderTransportProof.mem_mapSub_iff`, theorem
- `Langlands.JordanHolderTransportProof.quotientEquiv`, definition
- `Langlands.JordanHolderTransportProof.quotientEquiv._proof_1`, theorem
- `Langlands.JordanHolderTransportProof.quotientEquiv._proof_2`, theorem
- `Langlands.JordanHolderTransportProof.subrepOrderIso`, definition
- `Langlands.JordanHolderTransportProof.subrepOrderIso._proof_1`, theorem
- `Langlands.JordanHolderTransportProof.subrepOrderIso._proof_2`, theorem
- `Langlands.JordanHolderTransportProof.subrepOrderIso._proof_3`, theorem
- `Langlands.JordanHolderTransportProof.upperEquiv`, definition
- `Langlands.jordanHolderSeriesTransport`, theorem

### `Langlands.Representation.Filtration.LengthCriterionProof` (17)

- `Langlands.LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`, theorem
- `Langlands.LengthCriterionProof.hasSimpleFactors_iff_covBy`, theorem
- `Langlands.LengthCriterionProof.isIrreducible_quotientRep_iff`, theorem
- `Langlands.LengthCriterionProof.isIrreducible_quotientRep_iff._abel_1_1`, theorem
- `Langlands.LengthCriterionProof.lower`, definition
- `Langlands.LengthCriterionProof.lower_le_comap`, theorem
- `Langlands.LengthCriterionProof.mem_bot_iff`, theorem
- `Langlands.LengthCriterionProof.mem_top`, theorem
- `Langlands.LengthCriterionProof.mkQ_mem_bot_iff`, theorem
- `Langlands.LengthCriterionProof.pull`, definition
- `Langlands.LengthCriterionProof.pull._proof_1`, theorem
- `Langlands.LengthCriterionProof.pull._proof_2`, theorem
- `Langlands.LengthCriterionProof.push`, definition
- `Langlands.LengthCriterionProof.push._proof_1`, theorem
- `Langlands.LengthCriterionProof.push._proof_2`, theorem
- `Langlands.LengthCriterionProof.quotientRep`, definition
- `Langlands.LengthCriterionProof.quotientRep_mk`, theorem

### `Langlands.Representation.Filtration.LengthTwoMatching` (12)

- `Langlands.LengthTwo.isIrreducible_of_equiv`, theorem
- `Langlands.LengthTwo.oneStep`, definition
- `Langlands.LengthTwo.oneStep._proof_1`, theorem
- `Langlands.LengthTwo.oneStep._proof_2`, theorem
- `Langlands.LengthTwo.oneStep._proof_3`, theorem
- `Langlands.LengthTwo.oneStep._proof_4`, theorem
- `Langlands.LengthTwo.twoStep`, definition
- `Langlands.LengthTwo.twoStep._proof_1`, theorem
- `Langlands.LengthTwo.twoStep._proof_2`, theorem
- `Langlands.LengthTwo.twoStep._proof_3`, theorem
- `Langlands.LengthTwo.twoStep._proof_4`, theorem
- `Langlands.LengthTwo.twoStep._simp_1`, theorem

### `Langlands.Representation.Filtration.MultiplicityAdditivityProof` (10)

- `Langlands.MultiplicityAdditivityProof.card_selected_sigma`, theorem
- `Langlands.MultiplicityAdditivityProof.exists_series`, theorem
- `Langlands.MultiplicityAdditivityProof.quotient_bot_equiv`, theorem
- `Langlands.MultiplicityAdditivityProof.quotient_equiv_of_surjective`, theorem
- `Langlands.MultiplicityAdditivityProof.source_equiv_range`, theorem
- `Langlands.MultiplicityAdditivityProof.two_step_equivs`, theorem
- `Langlands.jordanHolderFiltrationAdditivity`, theorem
- `Langlands.jordanHolderFiltrationAdditivity.match_1_1`, definition
- `Langlands.jordanHolderFiltrationAdditivity.match_1_3`, definition
- `Langlands.jordanHolderShortExactAdditivity`, theorem

### `Langlands.Representation.Filtration.MultiplicityAdditivityStatement` (3)

- `Langlands.JordanHolderFiltrationAdditivityStatement`, definition
- `Langlands.JordanHolderShortExactAdditivityStatement`, definition
- `Langlands.JordanHolderShortExactAdditivityStatement._proof_1`, theorem

### `Langlands.Representation.Filtration.MultiplicityIndependenceProof` (4)

- `Langlands.HasJordanHolderMultiplicity.unique`, theorem
- `Langlands.jordanHolderMultiplicityIndependence`, theorem
- `Langlands.jordanHolderMultiplicityIndependence.match_1_1`, definition
- `Langlands.jordanHolderMultiplicityIndependence.match_1_3`, definition

### `Langlands.Representation.Filtration.MultiplicityStatement` (3)

- `Langlands.HasJordanHolderMultiplicity`, definition
- `Langlands.JordanHolderMultiplicityIndependenceStatement`, definition
- `Langlands.ObjectRepFiltration.factorMultiplicity`, definition

### `Langlands.Representation.Filtration.MultiplicityTransportProof` (4)

- `Langlands.equivCompositionSeriesMultiplicityTransport`, theorem
- `Langlands.equivCompositionSeriesMultiplicityTransport.match_1_1`, definition
- `Langlands.equivCompositionSeriesMultiplicityTransport.match_1_3`, definition
- `Langlands.equivJordanHolderMultiplicityTransport`, theorem

### `Langlands.Representation.Filtration.MultiplicityTransportStatement` (2)

- `Langlands.EquivCompositionSeriesMultiplicityTransportStatement`, definition
- `Langlands.EquivJordanHolderMultiplicityTransportStatement`, definition

### `Langlands.Representation.Filtration.ObjectDefinitions` (14)

- `Langlands.HasCompositionSeriesLength`, definition
- `Langlands.ObjectRepFiltration`, definition
- `Langlands.ObjectRepFiltration.HasSimpleFactors`, definition
- `Langlands.ObjectRepFiltration.gradedProjection`, definition
- `Langlands.ObjectRepFiltration.gradedProjection_surjective`, theorem
- `Langlands.ObjectRepFiltration.gradedRepresentation`, definition
- `Langlands.ObjectRepFiltration.monotone_subrepresentation`, theorem
- `Langlands.ObjectRepFiltration.ofSubrepresentations`, definition
- `Langlands.ObjectRepFiltration.ofSubrepresentations._proof_1`, theorem
- `Langlands.ObjectRepFiltration.subrepresentation`, definition
- `Langlands.ObjectRepFiltration.subrepresentation_last`, theorem
- `Langlands.ObjectRepFiltration.subrepresentation_zero`, theorem
- `Langlands.objectRepresentationFunctor`, definition
- `Langlands.objectRepresentationSubfunctor`, definition

### `Langlands.Representation.Filtration.SmoothGradedObject` (2)

- `Langlands.SmoothRep.IrreducibleGrothendieckProof.gradedSmooth`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.gradedSmooth._proof_1`, theorem

### `Langlands.Representation.Geometric.FlattenedLevi` (5)

- `Langlands.Geometric.flattenedLeviEquiv`, definition
- `Langlands.Geometric.flattenedLeviProductEquiv`, definition
- `Langlands.Geometric.flattenedLeviProductEquiv._proof_1`, theorem
- `Langlands.Geometric.flattenedLeviProductEquiv_apply`, theorem
- `Langlands.Geometric.flattenedLeviProductEquiv_apply_symm`, theorem

### `Langlands.Representation.Geometric.RefinementDefinitions` (45)

- `Langlands.Geometric.continuous_refinedLeviEval`, theorem
- `Langlands.Geometric.mem_refinedLevi`, theorem
- `Langlands.Geometric.mem_refinedLevi._simp_1`, theorem
- `Langlands.Geometric.mem_refinedLevi._simp_1_2`, theorem
- `Langlands.Geometric.mem_refinedParabolic`, theorem
- `Langlands.Geometric.mem_refinedParabolic._simp_1_2`, theorem
- `Langlands.Geometric.mem_refinedUnipotent`, theorem
- `Langlands.Geometric.mem_refinedUnipotent._simp_1_2`, theorem
- `Langlands.Geometric.mem_refinedUnipotentRadical`, theorem
- `Langlands.Geometric.refinedLeviEquiv`, definition
- `Langlands.Geometric.refinedLeviEquiv._proof_1`, theorem
- `Langlands.Geometric.refinedLeviEquiv._proof_2`, theorem
- `Langlands.Geometric.refinedLeviEquiv._proof_3`, theorem
- `Langlands.Geometric.refinedLeviEquiv._proof_4`, theorem
- `Langlands.Geometric.refinedLeviEquiv._proof_5`, theorem
- `Langlands.Geometric.refinedLeviEquiv._proof_6`, theorem
- `Langlands.Geometric.refinedLeviEquivContinuous`, definition
- `Langlands.Geometric.refinedLeviEquivContinuous._proof_1`, theorem
- `Langlands.Geometric.refinedLeviEquivContinuous._proof_2`, theorem
- `Langlands.Geometric.refinedLeviEval`, definition
- `Langlands.Geometric.refinedLeviEval._proof_1`, theorem
- `Langlands.Geometric.refinedLeviEval._proof_2`, theorem
- `Langlands.Geometric.refinedLeviEval._proof_3`, theorem
- `Langlands.Geometric.refinedLeviEval._proof_4`, theorem
- `Langlands.Geometric.refinedLeviEval._proof_5`, theorem
- `Langlands.Geometric.refinedLeviProjection`, definition
- `Langlands.Geometric.refinedLeviProjection_section`, theorem
- `Langlands.Geometric.refinedLeviSection`, definition
- `Langlands.Geometric.refinedLeviSection._proof_1`, theorem
- `Langlands.Geometric.refinedLeviSection._proof_2`, theorem
- `Langlands.Geometric.refinedLeviSection._proof_3`, theorem
- `Langlands.Geometric.refinedLeviSection._proof_4`, theorem
- `Langlands.Geometric.refinedLeviSection._proof_5`, theorem
- `Langlands.Geometric.refinedParabolicEval`, definition
- `Langlands.Geometric.refinedParabolicEval._proof_1`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_2`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_3`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_4`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_5`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_6`, theorem
- `Langlands.Geometric.refinedParabolicEval._proof_7`, theorem
- `Langlands.Geometric.refinedUnipotentPart`, definition
- `Langlands.Geometric.refinedUnipotentPart._proof_1`, theorem
- `Langlands.Geometric.refinedUnipotentRadical`, definition
- `Langlands.Geometric.block_mem_radical` (private), theorem

### `Langlands.Representation.Geometric.RefinementFunctors` (13)

- `Langlands.Geometric.normalizedRefinedInducedOf`, definition
- `Langlands.Geometric.normalizedRefinedInducedOf._proof_1`, theorem
- `Langlands.Geometric.normalizedRefinedInducedOfMap`, definition
- `Langlands.Geometric.normalizedRefinedInductionFunctorOf`, definition
- `Langlands.Geometric.normalizedRefinedInductionFunctorOf._proof_1`, theorem
- `Langlands.Geometric.normalizedRefinedInductionFunctorOf._proof_2`, theorem
- `Langlands.Geometric.normalizedRefinedInductionFunctorOf._proof_3`, theorem
- `Langlands.Geometric.normalizedRefinedJacquetFunctorOf._proof_1`, theorem
- `Langlands.Geometric.normalizedRefinedJacquetOf._proof_1`, theorem
- `Langlands.Geometric.refinedInducingMap`, definition
- `Langlands.Geometric.refinedInducingMap._proof_1`, theorem
- `Langlands.Geometric.refinedInducingMap._proof_2`, theorem
- `Langlands.Geometric.refinedInducingRepresentation`, definition

### `Langlands.Representation.Geometric.WeylDefinitions` (6)

- `Langlands.Geometric.BlockRefinement`, definition
- `Langlands.Geometric.blockIndex`, definition
- `Langlands.Geometric.blockIndex_index`, theorem
- `Langlands.Geometric.refinedLevi`, definition
- `Langlands.Geometric.refinedParabolic`, definition
- `Langlands.Geometric.refinedUnipotent`, definition

### `Langlands.Representation.Geometric.WeylMinimalRepresentativeProof` (2)

- `Langlands.Geometric.index_strictMono`, theorem
- `Langlands.Geometric.index_strictMono._proof_1_2`, theorem

### `Langlands.Representation.Geometric.WeylUniquenessProof` (2)

- `Langlands.Geometric.blockIndex_monotone`, theorem
- `Langlands.Geometric.exists_index_of_blockIndex_eq`, theorem

### `Langlands.Representation.Induction.BinaryProduct` (35)

- `Langlands.BinaryTensor.compEquiv`, definition
- `Langlands.BinaryTensor.compEquiv._proof_1`, theorem
- `Langlands.BinaryTensor.compMap`, definition
- `Langlands.BinaryTensor.compMap._proof_1`, theorem
- `Langlands.BinaryTensor.compMap._proof_2`, theorem
- `Langlands.BinaryTensor.firstFactorUnitEquiv`, definition
- `Langlands.BinaryTensor.firstFactorUnitEquiv._proof_1`, theorem
- `Langlands.BinaryTensor.isSmooth_lift`, theorem
- `Langlands.BinaryTensor.isSmooth_trivial`, theorem
- `Langlands.BinaryTensor.lift`, definition
- `Langlands.BinaryTensor.liftEquiv`, definition
- `Langlands.BinaryTensor.liftEquiv._proof_1`, theorem
- `Langlands.BinaryTensor.liftMap`, definition
- `Langlands.BinaryTensor.liftMap._proof_1`, theorem
- `Langlands.BinaryTensor.rankZeroLeft`, definition
- `Langlands.BinaryTensor.rankZeroLeft._proof_1`, theorem
- `Langlands.BinaryTensor.rankZeroLeft._proof_2`, theorem
- `Langlands.BinaryTensor.rankZeroLeftMap`, definition
- `Langlands.BinaryTensor.rankZeroLeftMap.eq_1`, theorem
- `Langlands.BinaryTensor.rankZeroLeftMap_comp`, theorem
- `Langlands.BinaryTensor.rankZeroLeftMap_id`, theorem
- `Langlands.BinaryTensor.rankZeroRight`, definition
- `Langlands.BinaryTensor.rankZeroRight._proof_1`, theorem
- `Langlands.BinaryTensor.rankZeroRight._proof_2`, theorem
- `Langlands.BinaryTensor.rankZeroRightMap`, definition
- `Langlands.BinaryTensor.rankZeroRightMap.eq_1`, theorem
- `Langlands.BinaryTensor.rankZeroRightMap_comp`, theorem
- `Langlands.BinaryTensor.rankZeroRightMap_id`, theorem
- `Langlands.BinaryTensor.secondFactorUnitEquiv`, definition
- `Langlands.BinaryTensor.secondFactorUnitEquiv._proof_1`, theorem
- `Langlands.BinaryTensor.secondFactorUnitEquiv._proof_2`, theorem
- `Langlands.BinaryTensor.secondFactorUnitEquiv._proof_3`, theorem
- `Langlands.BinaryTensor.secondFactorUnitEquiv._proof_4`, theorem
- `Langlands.GeneralLinear.representation_apply_of_rank_eq_zero`, theorem
- `Langlands.GeneralLinear.subsingleton_of_rank_eq_zero`, theorem

### `Langlands.Representation.Induction.BlockEquivalence` (4)

- `Langlands.GeneralLinear.BlockShape.productInducedOfEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.productInducedOfEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.productInducedOfEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.productInducedOfEquiv._proof_3`, theorem

### `Langlands.Representation.Induction.BlockFactors` (8)

- `Langlands.GeneralLinear.BlockShape.blockTensor`, definition
- `Langlands.GeneralLinear.BlockShape.productInducedOf`, definition
- `Langlands.GeneralLinear.BlockShape.productInducedOfMap`, definition
- `Langlands.GeneralLinear.BlockShape.productInducedOfMap.eq_1`, theorem
- `Langlands.GeneralLinear.BlockShape.productInducedOfMap_comp`, theorem
- `Langlands.GeneralLinear.BlockShape.productInducedOfMap_id`, theorem
- `Langlands.GeneralLinear.BlockShape.productInductionFunctorOf`, definition
- `Langlands.GeneralLinear.BlockShape.productInductionFunctorOf._proof_1`, theorem

### `Langlands.Representation.Induction.CompactLocalSection` (16)

- `Langlands.Induction.compactDoubleCosetSection`, definition
- `Langlands.Induction.compactDoubleCosetSection._proof_1`, theorem
- `Langlands.Induction.compactDoubleCosetSection_apply`, theorem
- `Langlands.Induction.compactDoubleCosetSection_support_subset`, theorem
- `Langlands.Induction.doubleCosetValue` (private), definition
- `Langlands.Induction.doubleCosetValue._proof_1` (private), theorem
- `Langlands.Induction.doubleCosetValue.eq_1` (private), theorem
- `Langlands.Induction.doubleCosetValue_covariant` (private), theorem
- `Langlands.Induction.doubleCosetValue_eq` (private), theorem
- `Langlands.Induction.doubleCosetValue_eq._simp_1_10` (private), theorem
- `Langlands.Induction.doubleCosetValue_eq._simp_1_2` (private), theorem
- `Langlands.Induction.doubleCosetValue_eq._simp_1_5` (private), theorem
- `Langlands.Induction.doubleCosetValue_eq._simp_1_7` (private), theorem
- `Langlands.Induction.doubleCosetValue_mul` (private), theorem
- `Langlands.Induction.doubleCosetValue_support_subset` (private), theorem
- `Langlands.Induction.inDoubleCoset` (private), definition

### `Langlands.Representation.Induction.CompactQuotientProof` (12)

- `Langlands.Induction.conjOpenSubgroup`, definition
- `Langlands.Induction.conjOpenSubgroup._proof_1`, theorem
- `Langlands.Induction.eval_covariant`, theorem
- `Langlands.Induction.eval_isLocallyConstant`, theorem
- `Langlands.Induction.eval_mem_fixedVectors`, theorem
- `Langlands.Induction.eval_mul_of_mem_fixedVectors`, theorem
- `Langlands.Induction.exists_finset_doubleCoset_cover`, theorem
- `Langlands.Induction.exists_finset_doubleCoset_cover._simp_1_1`, theorem
- `Langlands.Induction.isClosed_quotientSupport`, theorem
- `Langlands.Induction.mem_conjOpenSubgroup`, theorem
- `Langlands.Induction.quotientMap_preimage_quotientSupport`, theorem
- `OpenSubgroup.comap.congr_simp`, theorem

### `Langlands.Representation.Induction.ConjugateParabolic` (14)

- `Langlands.Induction.conjugateSmoothInducedEquiv`, definition
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_1`, theorem
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_2`, theorem
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_3`, theorem
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_4`, theorem
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_5`, theorem
- `Langlands.Induction.conjugateSmoothInducedEquiv._proof_6`, theorem
- `Langlands.Induction.translateSmoothFunction`, definition
- `Langlands.Induction.translateSmoothFunction._proof_1`, theorem
- `Langlands.Induction.translateSmoothFunction._proof_2`, theorem
- `Langlands.Induction.translateSmoothFunction._proof_3`, theorem
- `Langlands.Induction.conjugate_apply_inv` (private), theorem
- `Langlands.Induction.conjugate_symm_apply` (private), theorem
- `Langlands.Induction.conjugate_symm_rep` (private), theorem

### `Langlands.Representation.Induction.Definitions` (30)

- `Langlands.Induction.CompactFunctions`, definition
- `Langlands.Induction.EquivariantFunctions`, definition
- `Langlands.Induction.EquivariantFunctions._proof_1`, theorem
- `Langlands.Induction.SmoothCharacter`, inductive type
- `Langlands.Induction.SmoothCharacter.isOpen_ker`, theorem
- `Langlands.Induction.SmoothCharacter.mk`, constructor
- `Langlands.Induction.SmoothCharacter.toMonoidHom`, definition
- `Langlands.Induction.SmoothFunctions`, definition
- `Langlands.Induction.compactFunctions`, definition
- `Langlands.Induction.compactFunctions._proof_1`, theorem
- `Langlands.Induction.compactFunctions._proof_2`, theorem
- `Langlands.Induction.compactFunctions._proof_3`, theorem
- `Langlands.Induction.compactFunctions._proof_4`, theorem
- `Langlands.Induction.compactFunctions._proof_5`, theorem
- `Langlands.Induction.compactFunctions._proof_6`, theorem
- `Langlands.Induction.compactFunctions._simp_1`, theorem
- `Langlands.Induction.compactFunctions._simp_2`, theorem
- `Langlands.Induction.equivariantAction`, definition
- `Langlands.Induction.eval`, definition
- `Langlands.Induction.normalizedSmoothInduced`, definition
- `Langlands.Induction.quotientSupport`, definition
- `Langlands.Induction.smoothFunctionOf`, definition
- `Langlands.Induction.smoothFunctionOf._proof_1`, theorem
- `Langlands.Induction.smoothFunctionsAddCommGroup`, definition
- `Langlands.Induction.smoothInduced`, definition
- `Langlands.Induction.smoothInducedMap`, definition
- `Langlands.Induction.smoothInduced_smooth`, theorem
- `Langlands.Induction.eval_locallyConstant` (private), theorem
- `Langlands.Induction.preimage_quotientSupport` (private), theorem
- `Langlands.Induction.quotientSupport_closed` (private), theorem

### `Langlands.Representation.Induction.Equivalences` (6)

- `Langlands.Induction.smoothInducedEquiv`, definition
- `Langlands.Induction.smoothInducedEquiv._proof_1`, theorem
- `Langlands.Induction.smoothInducedEquiv._proof_2`, theorem
- `Langlands.Induction.smoothInducedEquiv._proof_3`, theorem
- `Langlands.Induction.smoothInducedEquiv._proof_4`, theorem
- `Langlands.Induction.smoothInducedEquiv._proof_5`, theorem

### `Langlands.Representation.Induction.FiniteProductTensor` (27)

- `Langlands.Induction.finiteProductTensorMap`, definition
- `Langlands.Induction.finiteProductTensorMap._proof_1`, theorem
- `Langlands.Induction.finiteProductTensorMap._proof_2`, theorem
- `Langlands.Induction.finiteProductTensorMap._proof_3`, theorem
- `Langlands.Induction.finiteProductTensorMap._proof_4`, theorem
- `Langlands.Induction.finiteProductTensorMap_tprod_eval`, theorem
- `Langlands.Induction.pointwiseTensorFunctions`, definition
- `Langlands.Induction.pointwiseTensorFunctions_apply`, theorem
- `Langlands.Induction.pointwiseTensorFunctions_covariant`, theorem
- `Langlands.Induction.pointwiseTensorFunctions_uniform`, theorem
- `Langlands.Induction.pointwiseTensorMultilinear`, definition
- `Langlands.Induction.pointwiseTensorMultilinear._proof_1`, theorem
- `Langlands.Induction.pointwiseTensorMultilinear._proof_2`, theorem
- `Langlands.Induction.productInducing`, definition
- `Langlands.Induction.productInducing_tprod`, theorem
- `Langlands.Induction.productSubgroupCoordinate`, definition
- `Langlands.Induction.productSubgroupCoordinate._proof_1`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_2`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_3`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_4`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_5`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_6`, theorem
- `Langlands.Induction.productSubgroupCoordinate._proof_7`, theorem
- `Langlands.Induction.factorEval` (private), definition
- `Langlands.Induction.factorEval._proof_1` (private), theorem
- `Langlands.Induction.factorEval._proof_2` (private), theorem
- `Langlands.Induction.pointwiseTensorCovariant` (private), definition

### `Langlands.Representation.Induction.FiniteProductTensorBijectiveProof` (44)

- `Langlands.Induction.FiniteProductTensorBijective.coefficientInclusion`, definition
- `Langlands.Induction.FiniteProductTensorBijective.doubleClass`, definition
- `Langlands.Induction.FiniteProductTensorBijective.evalLinear`, definition
- `Langlands.Induction.FiniteProductTensorBijective.evalLinear._proof_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.evalLinear._proof_2`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.evalLinear._proof_3`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_mem_fixedVectors_pi`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_mem_fixedVectors_pi._simp_1_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_mem_fixedVectors_pi._simp_1_4`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_mem_fixedVectors_pi._simp_1_7`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_productSection`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_productSection_of_ne`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_productSection_self`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.eval_sum`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.exists_compact_level`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.exists_decomposition`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.exists_level`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.finiteProductTensorMap_injective`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.finiteProductTensorMap_surjective`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.finite_doubleCosetQuotient`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.map_subtype_injective`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation`, definition
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation._proof_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation._proof_2`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation._proof_3`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation._proof_4`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.pointEvaluation._proof_5`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.productSection`, definition
- `Langlands.Induction.FiniteProductTensorBijective.productSection._proof_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.range_map_fixed_mono`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap`, definition
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap._proof_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap._proof_2`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap._proof_3`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap._proof_4`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.sectionMap._proof_5`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.section_eval_mul`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.section_eval_of_ne`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.section_eval_of_ne._simp_1_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.section_eval_of_ne._simp_1_3`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.section_eval_of_ne._simp_1_4`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.smoothFunctions_ext`, theorem
- `Langlands.Induction.FiniteProductTensorBijective.subtype_eq_sum`, theorem
- `Langlands.Induction.finiteProductTensorMap_bijective`, theorem

### `Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement` (5)

- `Langlands.Induction.FiniteProductTensorBijectiveTheorem`, definition
- `Langlands.Induction.FiniteProductTensorBijectiveTheorem._proof_1`, theorem
- `Langlands.Induction.FiniteProductTensorBijectiveTheorem._proof_2`, theorem
- `Langlands.Induction.FiniteProductTensorBijectiveTheorem._proof_3`, theorem
- `Langlands.Induction.FiniteProductTensorBijectiveTheorem._proof_4`, theorem

### `Langlands.Representation.Induction.HeterogeneousPairs` (3)

- `Langlands.literalULiftEquiv._proof_1`, theorem
- `Representation.Equiv.precomp`, definition
- `Representation.Equiv.precomp._proof_1`, theorem

### `Langlands.Representation.Induction.Parabolic` (18)

- `Langlands.GeneralLinear.BlockShape.inducingMap`, definition
- `Langlands.GeneralLinear.BlockShape.inducingMap._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.inducingMap._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.inducingRepresentation`, definition
- `Langlands.GeneralLinear.BlockShape.inflateCharacter`, definition
- `Langlands.GeneralLinear.BlockShape.inflateCharacter._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.inflateCharacter._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.isSmooth_normalizedInducedOf`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOf`, definition
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOf._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOf._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap`, definition
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap_comp`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInducedOfMap_id`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf`, definition
- `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.normalizedInductionFunctorOf._proof_3`, theorem

### `Langlands.Representation.Induction.SingleBlock` (21)

- `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv_symm_coordinate`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv`, definition
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_1`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_2`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_3`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_4`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_5`, theorem
- `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv._proof_6`, theorem
- `Langlands.Induction.smoothInducedTopEquiv`, definition
- `Langlands.Induction.smoothInducedTopEquiv._proof_1`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_10`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_11`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_12`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_2`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_3`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_4`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_5`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_6`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_7`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_8`, theorem
- `Langlands.Induction.smoothInducedTopEquiv._proof_9`, theorem

### `Langlands.Representation.Jacquet.Coinvariants` (1)

- `Langlands.Jacquet.relations._proof_1`, theorem

### `Langlands.Representation.Jacquet.PositiveCharacter` (5)

- `Langlands.Jacquet.complexCharacter`, definition
- `Langlands.Jacquet.inverseHalfCharacter`, definition
- `Langlands.Jacquet.inverseHalfCharacter_apply`, theorem
- `Langlands.Jacquet.inverseHalfCharacter_eq_one`, theorem
- `Langlands.Jacquet.positiveHalfCharacter`, definition

### `Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation` (1)

- `Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding`, theorem

### `Langlands.Representation.Parabolic.RefinementComposition` (4)

- `Langlands.Parabolic.composedLeviProjection`, definition
- `Langlands.Parabolic.composedLeviProjection._proof_1`, theorem
- `Langlands.Parabolic.composedLeviProjection._proof_2`, theorem
- `Langlands.Parabolic.composedParabolic`, definition

### `Langlands.Representation.Parabolic.RefinementPreimage` (32)

- `Langlands.Parabolic.leviPreimage`, definition
- `Langlands.Parabolic.leviPreimage_le_parabolic`, theorem
- `Langlands.Parabolic.mem_leviPreimage_iff`, theorem
- `Langlands.Parabolic.preimageInParabolic`, definition
- `Langlands.Parabolic.preimageInParabolic._proof_1`, theorem
- `Langlands.Parabolic.preimageInParabolic._proof_2`, theorem
- `Langlands.Parabolic.preimageInParabolic._proof_3`, theorem
- `Langlands.Parabolic.preimageInParabolic._proof_4`, theorem
- `Langlands.Parabolic.preimageInParabolic._proof_5`, theorem
- `Langlands.Parabolic.preimageInParabolic._proof_6`, theorem
- `Langlands.Parabolic.preimageProjection`, definition
- `Langlands.Parabolic.preimageProjection._proof_1`, theorem
- `Langlands.Parabolic.preimageProjection._proof_2`, theorem
- `Langlands.Parabolic.preimageProjection._proof_3`, theorem
- `Langlands.Parabolic.preimageProjection._proof_4`, theorem
- `Langlands.Parabolic.preimageProjection._proof_5`, theorem
- `Langlands.Parabolic.preimageProjection._proof_6`, theorem
- `Langlands.Parabolic.preimageProjection_radical`, theorem
- `Langlands.Parabolic.preimageProjection_section`, theorem
- `Langlands.Parabolic.preimageSection`, definition
- `Langlands.Parabolic.preimageSection._proof_1`, theorem
- `Langlands.Parabolic.preimageSection._proof_2`, theorem
- `Langlands.Parabolic.preimageSection._proof_3`, theorem
- `Langlands.Parabolic.preimageSection._proof_4`, theorem
- `Langlands.Parabolic.preimageSection._proof_5`, theorem
- `Langlands.Parabolic.radicalInPreimage`, definition
- `Langlands.Parabolic.radicalInPreimage._proof_1`, theorem
- `Langlands.Parabolic.radicalInPreimage._proof_2`, theorem
- `Langlands.Parabolic.radicalInPreimage._proof_3`, theorem
- `Langlands.Parabolic.radicalInPreimage._proof_4`, theorem
- `Langlands.Parabolic.radicalInPreimage._proof_5`, theorem
- `Langlands.Parabolic.radicalInPreimage._proof_6`, theorem

### `Langlands.Representation.Parabolic.RegroupingFactorEquivalences` (1)

- `Langlands.Parabolic.threeBlockSmoothFamily`, definition

### `Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry` (30)

- `Langlands.Parabolic.leftLabel`, definition
- `Langlands.Parabolic.leftLabel._proof_1`, theorem
- `Langlands.Parabolic.leftLabel.match_1`, definition
- `Langlands.Parabolic.leftLabelEquiv`, definition
- `Langlands.Parabolic.leftLabelEquiv._proof_1`, theorem
- `Langlands.Parabolic.leftLabelEquiv._proof_2`, theorem
- `Langlands.Parabolic.leftLabelEquiv_index`, theorem
- `Langlands.Parabolic.leftLabelEquiv_lex`, theorem
- `Langlands.Parabolic.leftLabelEquiv_size`, theorem
- `Langlands.Parabolic.leftLabelEquiv_val`, theorem
- `Langlands.Parabolic.leftLabelInv`, definition
- `Langlands.Parabolic.leftLabelInv._proof_1`, theorem
- `Langlands.Parabolic.leftLabelInv.match_1`, definition
- `Langlands.Parabolic.leftRefinement`, definition
- `Langlands.Parabolic.rightLabel`, definition
- `Langlands.Parabolic.rightLabel.match_1`, definition
- `Langlands.Parabolic.rightLabelEquiv`, definition
- `Langlands.Parabolic.rightLabelEquiv._proof_1`, theorem
- `Langlands.Parabolic.rightLabelEquiv._proof_2`, theorem
- `Langlands.Parabolic.rightLabelEquiv_index`, theorem
- `Langlands.Parabolic.rightLabelEquiv_lex`, theorem
- `Langlands.Parabolic.rightLabelEquiv_size`, theorem
- `Langlands.Parabolic.rightLabelEquiv_val`, theorem
- `Langlands.Parabolic.rightLabelInv`, definition
- `Langlands.Parabolic.rightRefinement`, definition
- `Langlands.Parabolic.threeBlocks`, definition
- `Langlands.Parabolic.threeBlocks._proof_1`, theorem
- `Langlands.Parabolic.threeBlocks._proof_2`, theorem
- `Langlands.Parabolic.threeBlocksRight`, definition
- `Langlands.Parabolic.threeBlocksRight._proof_1`, theorem

### `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly` (5)

- `Langlands.Parabolic.equivPrecomp`, definition
- `Langlands.Parabolic.equivPrecomp._proof_1`, theorem
- `Langlands.Parabolic.equivPrecomp._proof_2`, theorem
- `Langlands.Parabolic.equivSymm`, definition
- `Langlands.Parabolic.equivTrans`, definition

### `Langlands.Representation.Shahidi.Induction` (54)

- `Langlands.Shahidi.pairCarrier`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_1`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_12`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_14`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_16`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_24`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_26`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_3`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_31`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_35`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_37`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_39`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._aux_8`, definition
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_1`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_10`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_11`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_18`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_19`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_20`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_21`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_22`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_23`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_28`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_29`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_30`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_33`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_34`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_41`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_42`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_43`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_44`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_45`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_46`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_5`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_6`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup._proof_7`, theorem
- `Langlands.Shahidi.pairCarrier.instAddCommGroup.match_47`, definition
- `Langlands.Shahidi.pairCarrier.instModule`, definition
- `Langlands.Shahidi.pairCarrier.instModule._aux_1`, definition
- `Langlands.Shahidi.pairCarrier.instModule._aux_9`, definition
- `Langlands.Shahidi.pairCarrier.instModule._proof_11`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_12`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_13`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_14`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_15`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_16`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_3`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_4`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_5`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_6`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_7`, theorem
- `Langlands.Shahidi.pairCarrier.instModule._proof_8`, theorem
- `Langlands.Shahidi.pairFamily`, definition

### `Langlands.Representation.Shahidi.TwoBlocks` (3)

- `Langlands.Shahidi.twoBlocks`, definition
- `Langlands.Shahidi.twoBlocks._proof_1`, theorem
- `Langlands.Shahidi.twoBlocks._proof_2`, theorem

### `Langlands.Representation.Smooth.Definitions` (3)

- `Langlands.IsSmooth`, definition
- `Langlands.IsSmoothVector`, definition
- `Langlands.fixedVectors`, definition

### `Langlands.Representation.Smooth.FiniteLengthGrothendieck` (29)

- `Langlands.GeneralLinear.FiniteLengthGrothendieckGroup`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.IsExactAdditive`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.hom_ext`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift_ofClass`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift_ofRepresentation`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofClass`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofObject`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofObject_shortExact`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_shortExact`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.quotientMap`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.relations_le_ker_extend`, theorem
- `Langlands.SmoothRep.FiniteLengthIsoClass`, definition
- `Langlands.SmoothRep.FiniteLengthObject`, definition
- `Langlands.SmoothRep.FiniteLengthPresentation`, definition
- `Langlands.SmoothRep.IsShortExact`, definition
- `Langlands.SmoothRep.IsShortExact._proof_1`, theorem
- `Langlands.SmoothRep.finiteLengthIsoClass`, definition
- `Langlands.SmoothRep.finiteLengthIsoClass_eq_iff`, theorem
- `Langlands.SmoothRep.finiteLengthIsoSetoid`, definition
- `Langlands.SmoothRep.finiteLengthIsoSetoid._proof_1`, theorem
- `Langlands.SmoothRep.finiteLengthIsoSetoid.match_1`, definition
- `Langlands.SmoothRep.finiteLengthRelationSet`, definition
- `Langlands.SmoothRep.finiteLengthRelations`, definition

### `Langlands.Representation.Smooth.FiniteLengthGrothendieckBilinear` (14)

- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift₂`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift₂._proof_1`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift₂._proof_2`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.lift₂_ofClass`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapClass₂`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapClass₂._proof_1`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapClass₂._proof_2`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapClass₂_exact_left`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapClass₂_exact_right`, theorem
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.map₂`, definition
- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.map₂_objects`, theorem
- `Langlands.SmoothRep.PreservesFiniteLengthShortExactLeft`, definition
- `Langlands.SmoothRep.PreservesFiniteLengthShortExactRight`, definition
- `Langlands.SmoothRep.PreservesFiniteLength₂`, definition

### `Langlands.Representation.Smooth.IrreducibleCompositionFactors` (23)

- `Langlands.ObjectRepFiltration.factorMultiplicity.eq_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.chosenSeries`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.chosenSeries._proof_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.classFactors`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.classFactors._proof_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.classFactors_isExactAdditive`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors._proof_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_apply`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_eq_of_equiv`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_eq_series`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_irreducible`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_shortExact`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap_ofRepresentation`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.oneStep_graded_equiv`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.seriesClass`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.seriesClass.eq_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.seriesClass_apply`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.seriesClass_eq`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.seriesClass_eq_of_equiv`, theorem

### `Langlands.Representation.Smooth.IrreducibleGrothendieckProof` (15)

- `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation.congr_simp`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.factorMap_comp_realize`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.filtration_step_shortExact`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton._simp_1_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton._simp_1_2`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_comp_factorMap`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_seriesClass`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_seriesClass._abel_1_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_seriesClass._abel_1_3`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.realize_seriesClass._abel_1_4`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.subrepresentationTopEquiv`, definition
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.subrepresentationTopEquiv._proof_1`, theorem
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.subrepresentation_hasFiniteLength`, theorem
- `Langlands.SmoothRep.irreducibleGrothendieckStatement`, theorem

### `Langlands.Representation.Smooth.IrreducibleGrothendieckStatement` (1)

- `Langlands.SmoothRep.IrreducibleGrothendieckStatement`, definition

### `Langlands.Representation.Smooth.IrreducibleRealization` (21)

- `Langlands.SmoothRep.IrreducibleIsoClass`, definition
- `Langlands.SmoothRep.IrreducibleIsoClass.exists_eq`, theorem
- `Langlands.SmoothRep.IrreducibleIsoClass.toFiniteLengthIsoClass`, definition
- `Langlands.SmoothRep.IrreducibleIsoClass.toFiniteLengthIsoClass._proof_1`, theorem
- `Langlands.SmoothRep.IrreducibleIsoClass.toFiniteLengthIsoClass._proof_2`, theorem
- `Langlands.SmoothRep.IrreducibleLattice`, definition
- `Langlands.SmoothRep.IrreducibleObject`, definition
- `Langlands.SmoothRep.hasFiniteLength_of_isIrreducible`, theorem
- `Langlands.SmoothRep.irreducibleIsoClass`, definition
- `Langlands.SmoothRep.irreducibleIsoClass_eq_iff`, theorem
- `Langlands.SmoothRep.irreducibleIsoClass_eq_iff_nonempty_equiv`, theorem
- `Langlands.SmoothRep.irreducibleIsoClass_eq_iff_nonempty_equiv.match_1_1`, definition
- `Langlands.SmoothRep.irreducibleIsoClass_eq_iff_nonempty_equiv.match_1_3`, definition
- `Langlands.SmoothRep.irreducibleIsoClass_eq_of_equiv`, theorem
- `Langlands.SmoothRep.irreducibleIsoSetoid`, definition
- `Langlands.SmoothRep.irreducibleIsoSetoid._proof_1`, theorem
- `Langlands.SmoothRep.irreducibleIsoSetoid.match_1`, definition
- `Langlands.SmoothRep.realizeIrreducibles`, definition
- `Langlands.SmoothRep.realizeIrreducibles_generator`, theorem
- `Langlands.SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass`, theorem
- `Langlands.SmoothRep.realizeIrreducibles_zero`, theorem

### `Langlands.Representation.Smooth.SmoothPart.BasicProof` (2)

- `Langlands.isSmoothVector_add`, theorem
- `Langlands.isSmoothVector_smul`, theorem

### `Langlands.Representation.Smooth.SmoothPart.Definitions` (15)

- `Langlands.smoothInclusion`, definition
- `Langlands.smoothInclusion._proof_1`, theorem
- `Langlands.smoothInclusion._proof_2`, theorem
- `Langlands.smoothLift`, definition
- `Langlands.smoothLift._proof_1`, theorem
- `Langlands.smoothLift._proof_2`, theorem
- `Langlands.smoothMap`, definition
- `Langlands.smoothMap._proof_1`, theorem
- `Langlands.smoothPart`, definition
- `Langlands.smoothSubrepresentation`, definition
- `Langlands.smoothSubrepresentation._proof_1`, theorem
- `Langlands.smoothVectors`, definition
- `Langlands.smoothVectors._proof_1`, theorem
- `Langlands.smoothVectors._proof_2`, theorem
- `Langlands.smoothVectors._proof_3`, theorem

### `Langlands.Representation.Smooth.Transfer.PullbackProof` (2)

- `Langlands.isSmoothVector_comp`, theorem
- `Langlands.isSmooth_comp`, theorem

### `Langlands.Representation.Smooth.Transfer.SubquotientProof` (4)

- `Langlands.isSmoothVector_map`, theorem
- `Langlands.isSmoothVector_of_injective`, theorem
- `Langlands.isSmooth_of_injective`, theorem
- `Langlands.isSmooth_of_surjective`, theorem

### `Langlands.Representation.Tensor.Finite` (21)

- `Langlands.FiniteTensor.action`, definition
- `Langlands.FiniteTensor.action._proof_1`, theorem
- `Langlands.FiniteTensor.action._proof_2`, theorem
- `Langlands.FiniteTensor.action_tprod`, theorem
- `Langlands.FiniteTensor.external`, definition
- `Langlands.FiniteTensor.externalFunctor`, definition
- `Langlands.FiniteTensor.externalFunctor._proof_1`, theorem
- `Langlands.FiniteTensor.externalFunctor._proof_2`, theorem
- `Langlands.FiniteTensor.externalMap`, definition
- `Langlands.FiniteTensor.externalMap._proof_1`, theorem
- `Langlands.FiniteTensor.externalMap_comp`, theorem
- `Langlands.FiniteTensor.externalMap_id`, theorem
- `Langlands.FiniteTensor.externalSmoothObject`, definition
- `Langlands.FiniteTensor.externalSmoothObject._proof_1`, theorem
- `Langlands.FiniteTensor.external_tprod`, theorem
- `Langlands.FiniteTensor.isSmoothVector_tprod`, theorem
- `Langlands.FiniteTensor.isSmooth_action`, theorem
- `Langlands.FiniteTensor.isSmooth_external`, theorem
- `Langlands.FiniteTensor.map`, definition
- `Langlands.FiniteTensor.map._proof_1`, theorem
- `Langlands.FiniteTensor.map._proof_2`, theorem

### `Langlands.Representation.Tensor.FiniteEquivalences` (15)

- `Langlands.FiniteTensor.evalOne`, definition
- `Langlands.FiniteTensor.evalOneContinuous`, definition
- `Langlands.FiniteTensor.evalOneContinuous._proof_1`, theorem
- `Langlands.FiniteTensor.evalOneContinuous._proof_2`, theorem
- `Langlands.FiniteTensor.evalOneContinuous._proof_3`, theorem
- `Langlands.FiniteTensor.evalOne_symm_zero`, theorem
- `Langlands.FiniteTensor.headTail._proof_1`, theorem
- `Langlands.FiniteTensor.headTailLinearEquiv`, definition
- `Langlands.FiniteTensor.headTailLinearEquiv._proof_1`, theorem
- `Langlands.FiniteTensor.headTailLinearEquiv._proof_2`, theorem
- `Langlands.FiniteTensor.headTailLinearEquiv_tprod`, theorem
- `Langlands.FiniteTensor.singletonEquiv`, definition
- `Langlands.FiniteTensor.singletonEquiv._proof_1`, theorem
- `Langlands.FiniteTensor.singletonEquiv_apply_action`, theorem
- `Langlands.FiniteTensor.headTailIndex` (private), definition

### `Langlands.Representation.Tensor.FiniteProperties` (8)

- `Langlands.FiniteTensor.external_mulSingle`, theorem
- `Langlands.FiniteTensor.fixedVectors_external_le`, theorem
- `Langlands.FiniteTensor.lTensor_eq_of_forall_fixed`, theorem
- `Langlands.FiniteTensor.map_eq_of_forall_fixed`, theorem
- `Langlands.FiniteTensor.map_induction`, theorem
- `Langlands.FiniteTensor.map_slot_eq_of_forall_fixed`, theorem
- `Langlands.FiniteTensor.slot`, definition
- `Langlands.FiniteTensor.split_map_slot`, theorem

### `Langlands.Representation.Tensor.FiniteRegrouping` (12)

- `Langlands.FiniteTensor.regroupLinearEquiv`, definition
- `Langlands.FiniteTensor.regroupLinearEquiv._proof_1`, theorem
- `Langlands.FiniteTensor.regroupLinearEquiv_tprod`, theorem
- `Langlands.FiniteTensor.sigmaRegroupLinearEquiv`, definition
- `Langlands.FiniteTensor.sigmaRegroupLinearEquiv._proof_1`, theorem
- `Langlands.FiniteTensor.sigmaRegroupLinearEquiv_tprod`, theorem
- `Langlands.FiniteTensor.finRegroup_exists` (private), theorem
- `Langlands.FiniteTensor.sigmaFinSucc` (private), definition
- `Langlands.FiniteTensor.sigmaFinSucc._proof_1` (private), theorem
- `Langlands.FiniteTensor.sigmaFinSucc._proof_2` (private), theorem
- `Langlands.FiniteTensor.sigmaFinSucc._proof_3` (private), theorem
- `Langlands.FiniteTensor.sigmaRegroup_exists` (private), theorem

### `Langlands.Representation.Tensor.OneFactor` (15)

- `Langlands.BinaryTensor.firstFactor`, definition
- `Langlands.BinaryTensor.firstFactorMap`, definition
- `Langlands.BinaryTensor.firstFactorMap._proof_1`, theorem
- `Langlands.BinaryTensor.firstFactorMap_comp`, theorem
- `Langlands.BinaryTensor.firstFactorMap_id`, theorem
- `Langlands.BinaryTensor.firstFactor_tmul`, theorem
- `Langlands.BinaryTensor.isSmooth_firstFactor`, theorem
- `Langlands.BinaryTensor.isSmooth_secondFactor`, theorem
- `Langlands.BinaryTensor.secondFactor`, definition
- `Langlands.BinaryTensor.secondFactorMap`, definition
- `Langlands.BinaryTensor.secondFactorMap._proof_1`, theorem
- `Langlands.BinaryTensor.secondFactorMap._proof_2`, theorem
- `Langlands.BinaryTensor.secondFactorMap_comp`, theorem
- `Langlands.BinaryTensor.secondFactorMap_id`, theorem
- `Langlands.BinaryTensor.secondFactor_tmul`, theorem

### `Langlands.Representation.Twist.Definitions` (7)

- `Langlands.twist`, definition
- `Langlands.twist._proof_1`, theorem
- `Langlands.twist._proof_2`, theorem
- `Langlands.twist._proof_3`, theorem
- `Langlands.twistIntertwining`, definition
- `Langlands.twistIntertwining._proof_1`, theorem
- `Langlands.twistIntertwining._proof_2`, theorem

### `Langlands.Representation.Whittaker.Iwasawa` (22)

- `Langlands.GeneralLinear.Iwasawa.det_eq_last_mul_det_castSucc`, theorem
- `Langlands.GeneralLinear.Iwasawa.div_mem_integer`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_clear_last_row`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_clear_last_row._abel_1_1`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_clear_last_row._abel_1_2`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_last_dominant`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_mul_upperTriangular`, theorem
- `Langlands.GeneralLinear.Iwasawa.exists_mul_upperTriangular._f`, definition
- `Langlands.GeneralLinear.Iwasawa.exists_mul_upperTriangular.match_1_1`, definition
- `Langlands.GeneralLinear.Iwasawa.integralRange`, definition
- `Langlands.GeneralLinear.Iwasawa.integralRange_succ`, theorem
- `Langlands.GeneralLinear.Iwasawa.lastRowClearing`, definition
- `Langlands.GeneralLinear.Iwasawa.lastRowClearing_mul_self`, theorem
- `Langlands.GeneralLinear.Iwasawa.ofInverse`, definition
- `Langlands.GeneralLinear.Iwasawa.ofInverse_mem`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_castSucc_castSucc`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_castSucc_last`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_last_castSucc`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_last_last`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_map`, theorem
- `Langlands.GeneralLinear.Iwasawa.rankInclusion_mem`, theorem
- `Langlands.GeneralLinear.Iwasawa.transvection_mem`, theorem

### `Langlands.Topology.CompactOpen.NeighborhoodBasis` (1)

- `Langlands.compactOpenSubgroupBasis`, theorem

### `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` (1)

- `Langlands.CompactOpenSubgroupBasis`, definition

### `Langlands.VirtualRepresentation.Integral` (3)

- `Langlands.VirtualRepresentation.IntegralLattice`, definition
- `Langlands.VirtualRepresentation.extend`, definition
- `Langlands.VirtualRepresentation.generator`, definition
