# Reducing the L-factor characterization of the assembly to its ingredients

Author: Worker 1700.

This module proves Henniart 2002, Theorem 1.8 (printed p. 591; proof in §4.5,
printed p. 600, PDF p. 14) conditionally. The published proposition
`AssemblyLCharacterizationStatement F` is derived from five Library statements,
bundled in `AssemblyLCharacterizationIngredients F`. None of the five is proved
here. The module does not prove `AssemblyLCharacterizationStatement` outright.

## The ingredients

`AssemblyLCharacterizationIngredients F` (a `Prop`) is the conjunction of:

1. `AssemblyWellDefinedStatement F`.
2. `AssemblyBijectiveStatement F`.
3. `AssemblyLInheritanceStatement F`.
4. `RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement` at the
   universes `uF, uA, uA` (Henniart's Theorem 1.7(b)).
5. `AssemblySquareIntegrablePreimageStatement F`: a parameter assembled to an
   essentially square-integrable class is indecomposable (Henniart §§2.6–2.9).

All five use the same universes `uF, uP, uA` as the target.
`AssemblyExtendsStatement` is not an ingredient. The target's hypothesis that
`τ` extends `c0` supplies the zero-monodromy classes, and the proved
single-block witness of `AssemblyZeroMonodromyWitness` gives the values of
every assembly on them.

## Provenance (internal)

The bundle is an internal device: Henniart's §4.5 uses exactly these facts.
Well-definedness, bijectivity and L-inheritance come from §2 and Theorem 1.5,
the fourth is Theorem 1.7(b), and the fifth comes from the classification in
§§2.6–2.9.

## Lemmas

- `isSupercuspidal_rank_one`: every irreducible admissible representation of
  `GL_1(F)` is supercuspidal. The only block shape of rank one has one block:
  its length is at most 1 (`BlockShape.length_le`) and not 0 (an empty sum
  is not 1). A one-block parabolic is the whole group
  (`BlockShape.singleBlock_parabolic_eq_top`), so the Jacquet-module
  condition of `GeneralLinear.IsSupercuspidal` is vacuous.
- `extendsSupercuspidal_of_isAssemblyOf`: under ingredient 1, an assembly `c`
  of `c0` extends `c0` whenever some full map `τ` does. For each `σ`, `τ`
  provides a zero-monodromy class `E` of `σ`, and
  `assembly_apply_of_isZeroMonodromyOf` gives `c E = c0 σ`.
- `isIrreducibleWeilParameter_of_isSupercuspidal`: take `c0` surjective in
  every rank, `c` an extension of `c0` (`ExtendsSupercuspidal`) and `c`
  injective in every rank. If `c n D` is the class of a supercuspidal object
  `A`, then `D` is an irreducible Weil parameter. Bundle `A` as a
  `SupercuspidalRep` and choose a preimage `σ` under `c0`. The extension gives
  a zero-monodromy class `E` of `σ` with `c n E = c0 σ = c n D`, and
  injectivity gives `E = D`.
- `assembly_eq_of_lowerRankPairL`: Henniart's induction. Assume all five
  ingredients, a supercuspidal correspondence `c0`, a full map `τ` extending `c0`, a
  nontrivial additive character `ψ`, and the lower-rank hypothesis of the
  target for `τ` at `ψ`. Then every assembly `c` of `c0` equals `τ`.

## Proof of the induction

Fix an assembly `c`. By `extendsSupercuspidal_of_isAssemblyOf` and
ingredients 2 and 3, `c` extends `c0`, is bijective in every rank, and has the
L-inheritance property at `ψ`. The
correspondence `c0` supplies a self-dual measure `ν` for `ψ`
(`IsSupercuspidalCorrespondence.exists_selfDualMeasure`). By strong induction
on `k`, `c (k+1) D = τ (k+1) D` for every class `D` of rank `k + 1`:

- If `D` is an irreducible Weil parameter, `c` and `τ` agree on `D` because
  both extend `c0` (`ExtendsSupercuspidal.eq_on_irreducible`, Worker 422's
  `ZeroMonodromyExtension`).
- Otherwise, choose representatives `A` of `c D` and `B` of `τ D`. By the
  previous lemma, `A` is not supercuspidal. In rank 1 this contradicts
  `isSupercuspidal_rank_one`.
- In rank `n + 2`, apply `automorphicClass_eq_of_pole_order_tests` (Worker
  422's `AutomorphicPoleComparison`) with ingredient 4, `ψ` and `ν`. It
  remains to compare pole orders against each essentially square-integrable
  object `R` of rank `r + 1 ≤ n + 1`. Surjectivity of `c` gives `D'` with
  `c D' = [R]`. Ingredient 5 makes `D'` indecomposable, and the induction
  hypothesis gives `c D' = τ D'`. L-inheritance for `c` and the target's
  hypothesis for `τ` give two pair-L compatibilities of `(D, D')` with the
  same second image. `IsPairLCompatibleAt.same_pole_order` (Worker 422's
  `PairLCompatibilityComparison`) turns them into certified polynomials with
  equal pole orders, which are the required tests after rewriting by the
  representatives.

Every positive rank is `k.succPNat` for some `k`, which gives `c = τ`.

## Main theorem

`assemblyLCharacterization_of_ingredients` proves
`AssemblyLCharacterizationIngredients F → AssemblyLCharacterizationStatement F`.
Given `c0`, `τ`, `ψ` and the hypotheses of the target, the existence half of
ingredient 1 provides an assembly `c`. This is the published choice
`assemblyOfWellDefined F hwd c0` with its law
`assemblyOfWellDefined_isAssemblyOf` (`AssemblyConstruction`, Worker 864).
The induction gives `c = τ`, so
`τ` is an assembly of `c0`. Applied to any other assembly `c'`, it gives
`c' = τ`. The uniqueness half of ingredient 1 is used only pointwise, on
zero-monodromy classes.

## Names of the file-local topologies

The two file-local instances are named `assemblyLCharacterizationFieldTopology` and
`assemblyLCharacterizationGeneralLinearTopology`. They used to be named
`assemblyReductionFieldTopology` and `assemblyReductionGeneralLinearTopology`, the names
under which `AssemblyBijectiveReduction` declares its own copies of the same two
topologies. A file-local instance is still a declaration in the namespace
`Langlands.Correspondence`. Neither module imports the other, so each built on its own,
but any module or kernel replay that loads both met each of the two names twice. Only
the names changed: types and values are as before, and no other module refers to these
instances by name.

## Declaration names made distinct in the Library (Task 5265)

This module's record carries all renames of Task 5265, which gives distinct names to
declarations that two Library modules declared under one name. Neither module of each pair
imports the other, so each built on its own, but any module or kernel replay that loads
both met the name twice. In each pair one module keeps the name and the other declares
the same declaration under a new explicit name: an instance becomes
`instance <name> : ...`, and a lemma or theorem gets a new name with every use updated.
Only names change. Types, values, attributes and all other declarations are as before,
and no file outside the renamed modules refers to a renamed declaration by name.
Auxiliary names derived from a renamed declaration, such as `_proof_N` or a `_assoc`
lemma, follow its new name.

For each module: the old full name, the new name in the same namespace, and the module
that keeps the old name.

- `Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof`:
  - `Langlands.AbelianScheme.hom_baseChange_map_fst` is now `hom_baseChange_map_fst'` (kept by `Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof`).
- `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardDerived`:
  - `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward.instIsEquivalenceSheafAddCommGrpCatPushforwardHomTopCat_langlands_1` is now `instIsEquivalencePushforward_unitSheafPushforwardDerived` (kept by `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardComposition`).
  - `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward.instAdditiveSheafAddCommGrpCatPushforwardHomTopCat_langlands_1` is now `instAdditivePushforward_unitSheafPushforwardDerived` (kept by `Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardComposition`).
- `Langlands.Automorphic.CuspidalUnitaryForm`:
  - `Langlands.Automorphic.OperatorRealization.instAddCommGroupSubtypeForallAdelicGLComplexMemSubmoduleRationalInvariantFunctionsContinuousRationalFunctionsFiniteSmoothRationalFunctionsStableAutomorphicFunctionsSpace_3` is now `instAddCommGroupSpace_cuspidalUnitaryForm` (kept by `Langlands.Automorphic.DeterminantTwistFiniteSlice`).
- `Langlands.Automorphic.HorizontalDegreeZero`:
  - `Langlands.Automorphic.OperatorRealization.instAddCommGroupSubtypeAlternatingMapComplexReducedComplexLieAlgebraForallAdelicGLMemSubmoduleRationalInvariantFunctionsContinuousRationalFunctionsFiniteSmoothRationalFunctionsStableAutomorphicFunctionsSpaceFinHorizontalEquivariantSubmoduleCompactRepresentation_1` is now `horizontalZeroEquivariantAddCommGroup` (kept by `Langlands.Automorphic.HorizontalCohomologyClasses`).
- `Langlands.Cohomology.Lie.HorizontalDegreeZero`:
  - `Langlands.Cohomology.Lie.Horizontal.instAddCommGroupSubtypeAlternatingMapFinMemSubmoduleSubmoduleCycles_1` is now `instAddCommGroupCycles_lieHorizontalDegreeZero` (kept by `Langlands.Cohomology.Lie.HorizontalCohomologyAction`).
- `Langlands.Correspondence.AssemblyLCharacterizationReduction`:
  - `Langlands.Correspondence.assemblyReductionFieldTopology` is now `assemblyLCharacterizationFieldTopology` (kept by `Langlands.Correspondence.AssemblyBijectiveReduction`).
  - `Langlands.Correspondence.assemblyReductionGeneralLinearTopology` is now `assemblyLCharacterizationGeneralLinearTopology` (kept by `Langlands.Correspondence.AssemblyBijectiveReduction`).
- `Langlands.Correspondence.AutomorphicGammaRigidity`:
  - `Langlands.Correspondence.instTopologicalSpaceCarrier_5` is now `instTopologicalSpaceCarrier_automorphicGammaRigidity` (kept by `Langlands.Correspondence.ArithmeticSystemComparison`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartSpectralRestriction`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup` is now `instIsTopologicalGroupOpenSubgroup_rationalChartSpectralRestriction` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantActions`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantOverBase`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup_2` is now `instIsTopologicalGroupOpenSubgroup_rationalNormInvariantOverBase` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantPresheaf`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantActions`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup_1` is now `instIsTopologicalGroupOpenSubgroup_rationalSpectralInvariantActions` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantRestriction`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralLocallyConstantPresheaf`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup_2` is now `instIsTopologicalGroupOpenSubgroup_rationalSpectralLocallyConstantPresheaf` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantPresheaf`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralLocallyConstantSheaf`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup_3` is now `instIsTopologicalGroupOpenSubgroup_rationalSpectralLocallyConstantSheaf` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantSheaf`).
- `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralLocallyConstantSmoothSheaf`:
  - `Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.instIsTopologicalGroupSubtypeMemOpenSubgroup_3` is now `instIsTopologicalGroupOpenSubgroup_rationalSpectralLocallyConstantSmoothSheaf` (kept by `Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantSheaf`).
- `Langlands.Geometry.Building.AffineFacetIntersections`:
  - `Langlands.Geometry.Building.AffineRootSystem.instDecidableEq_langlands` is now `instDecidableEq_affineFacetIntersections` (kept by `Langlands.Geometry.Building.AffineFacetSimplicialFaces`).
- `Langlands.Geometry.Building.BuildingFacetIntersections`:
  - `Langlands.Geometry.Building.ParahoricBuildingData.IsBuildingTitsSystem.instDecidableEqReducedBuilding` is now `instDecidableEqReducedBuilding_buildingFacetIntersections` (kept by `Langlands.Geometry.Building.TitsFacetVertexEmbedding`).
- `Langlands.Global.IntegralFiniteAdelePadicProduct`:
  - `Langlands.Global.instFactPrimeValNat_langlands` is now `instFactPrimeVal_integralFiniteAdelePadicProduct` (kept by `Langlands.Global.ProfiniteIntegerPadicProductComparison`).
- `Langlands.Global.PrimeToIntegralProfiniteIntegerComparisonProof`:
  - `Langlands.Global.instFactPrimeValNat_langlands_1` is now `instFactPrimeVal_primeToIntegralProfiniteIntegerComparisonProof` (kept by `Langlands.Global.ProfiniteIntegerPadicProductComparisonProof`).
- `Langlands.GroupScheme.Examples.SU3RootParametersHenselianValuation`:
  - `Langlands.GroupScheme.SU3Root.instFiniteDimensional` is now `instFiniteDimensional_su3RootParametersHenselianValuation` (kept by `Langlands.GroupScheme.Examples.SU3RootParametersTowerValuation`).
- `Langlands.GroupScheme.IntegralModel.SpectralIntegralPointAction`:
  - `Langlands.GroupScheme.IntegralModel.instNontriviallyNormedField` is now `instNontriviallyNormedField_spectralIntegralPointAction` (kept by `Langlands.GroupScheme.IntegralModel.UnramifiedIntegralPointAction`).
  - `Langlands.GroupScheme.IntegralModel.instIsUltrametricDist` is now `instIsUltrametricDist_spectralIntegralPointAction` (kept by `Langlands.GroupScheme.IntegralModel.UnramifiedIntegralPointAction`).
  - `Langlands.GroupScheme.IntegralModel.instCompleteSpace` is now `instCompleteSpace_spectralIntegralPointAction` (kept by `Langlands.GroupScheme.IntegralModel.UnramifiedIntegralPointAction`).
- `Langlands.GroupScheme.Lie.WeightGaloisFixedDescent`:
  - `Langlands.GroupScheme.instIsAffineHomHomSchemeXOverSpecOfObjBaseChangeAlgebraBaseMap_4` is now `instIsAffineHomBaseChange_weightGaloisFixedDescent` (kept by `Langlands.GroupScheme.Lie.SplitRootWeightGaloisCoordinates`).
- `Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning`:
  - `Langlands.GroupScheme.instIsAffineHomHomSchemeXOverSpecOfObjBaseChangeAlgebraBaseMap_4` is now `instIsAffineHomBaseChange_quasiSplitCompatiblePinning` (kept by `Langlands.GroupScheme.Lie.SplitRootWeightGaloisCoordinates`).
- `Langlands.GroupScheme.Rational.QuasiSplitPinningOrbitPairs`:
  - `Langlands.GroupScheme.instIsAffineHomHomSchemeXOverSpecOfObjBaseChangeAlgebraBaseMap_5` is now `instIsAffineHomBaseChange_quasiSplitPinningOrbitPairs` (kept by `Langlands.GroupScheme.Lie.RootOrbitLineCoordinates`).
- `Langlands.GroupScheme.Rational.RootFiberTransitivity`:
  - `Langlands.GroupScheme.instIsAffineHomHomSchemeXOverSpecOfObjBaseChangeAlgebraBaseMap_3` is now `instIsAffineHomBaseChange_rootFiberTransitivity` (kept by `Langlands.GroupScheme.Lie.WeightLineGaloisCoordinates`).
- `Langlands.GroupScheme.Rational.SteinbergIndependentWeightReduction`:
  - `Langlands.GroupScheme.SplitPinning.instMonoSchemeLeftHomOverSpecOfHomGrpMonInclusion_2` is now `instMonoInclusion_steinbergIndependentWeightReduction` (kept by `Langlands.GroupScheme.Rational.ModifiedProductImmersion`).
- `Langlands.GroupScheme.Reductive.CovariantUnipotentFixedLine`:
  - `Langlands.GroupScheme.instIsAffineLeftSchemeXOverSpecOf` is now `instIsAffineLeftG_covariantUnipotentFixedLine` (kept by `Langlands.GroupScheme.Rational.BruhatOpenCellReduction`).
  - `Langlands.GroupScheme.instIsAffineLeftSchemeXOverSpecOf_1` is now `instIsAffineLeftH_covariantUnipotentFixedLine` (kept by `Langlands.GroupScheme.Rational.BruhatOpenCellProof`).
- `Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry`:
  - `Langlands.GroupScheme.AffineCoordinates.instIsAffineLeftSchemeXOverSpecOf_2` is now `instIsAffineLeft_steinbergBigCellGeometry` (kept by `Langlands.GroupScheme.Reductive.NormalizedCovariantCharacter`).
- `Langlands.GroupScheme.SpecialLinearBinaryBigCell`:
  - `Langlands.GroupScheme.SpecialLinear.BinaryUpper.instIsAffineLeftSchemeXOverSpecOfGroupSchemeFinOfNatNat_1` is now `instIsAffineSpecialLinearLeft_specialLinearBinaryBigCell` (kept by `Langlands.GroupScheme.SpecialLinearBinaryCovariant`).
  - `Langlands.GroupScheme.SpecialLinear.BinaryUpper.instIsAffineLeftSchemeXOverSpecOfGroupScheme_1` is now `instIsAffineBinaryUpperLeft_specialLinearBinaryBigCell` (kept by `Langlands.GroupScheme.SpecialLinearBinaryCovariant`).
  - `Langlands.GroupScheme.SpecialLinear.BinaryUpper.instIsAffineHomHomSchemeXOverSpecOfGroupScheme` is now `instIsAffineHomBinaryUpper_specialLinearBinaryBigCell` (kept by `Langlands.GroupScheme.SpecialLinearBinaryCovariant`).
  - `Langlands.GroupScheme.SpecialLinear.BinaryUpper.instIsAffineHomHomSchemeXOverSpecOfGroupSchemeFinOfNatNat` is now `instIsAffineHomSpecialLinear_specialLinearBinaryBigCell` (kept by `Langlands.GroupScheme.SpecialLinearBinaryCovariant`).
- `Langlands.GroupScheme.SpecialLinearBinaryRegular`:
  - `Langlands.GroupScheme.SpecialLinear.BinaryUpper.instIsAffineLeftSchemeXOverSpecOfGroupSchemeFinOfNatNat_2` is now `instIsAffineSpecialLinearLeft_specialLinearBinaryRegular` (kept by `Langlands.GroupScheme.SpecialLinearBinaryRegularAction`).
- `Langlands.LocalFactor.Abelian.Gamma`:
  - `Langlands.PadicField.AbelianTransport.instTopologicalSpaceCarrier_4` is now `instTopologicalSpaceCarrierF_abelianGamma` (kept by `Langlands.LocalFactor.Abelian.SelfDualTransport`).
  - `Langlands.PadicField.AbelianTransport.instTopologicalSpaceCarrier_5` is now `instTopologicalSpaceCarrierE_abelianGamma` (kept by `Langlands.LocalFactor.Abelian.SelfDualTransport`).
  - `Langlands.PadicField.AbelianTransport.instMeasurableSpaceCarrier_4` is now `instMeasurableSpaceCarrierF_abelianGamma` (kept by `Langlands.LocalFactor.Abelian.SelfDualTransport`).
  - `Langlands.PadicField.AbelianTransport.instMeasurableSpaceCarrier_5` is now `instMeasurableSpaceCarrierE_abelianGamma` (kept by `Langlands.LocalFactor.Abelian.SelfDualTransport`).
- `Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStatement`:
  - `Langlands.CuspidalSupport.instTopologicalSpaceRationalPoints_2` is now `instTopologicalSpaceRationalPoints_rationalNormKernelHeckeStatement` (kept by `Langlands.Representation.CuspidalSupport.RationalInertiaPresentations`).
- `Langlands.Representation.Jacquet.StandardCanonicalSectionProof`:
  - `Langlands.Jacquet.instIsAffineLeftSchemeXOverSpecOf_langlands` is now `instIsAffineLeft_standardCanonicalSectionProof` (kept by `Langlands.Representation.Jacquet.StandardGeneralizedJacquetLift`).
  - `Langlands.Jacquet.instTopologicalSpaceRationalPoints` is now `instTopologicalSpaceRationalPoints_standardCanonicalSectionProof` (kept by `Langlands.Representation.Jacquet.StandardGeneralizedJacquetLift`).
- `Langlands.Shimura.Coefficients.EtaleAssociatedPullback`:
  - `Langlands.Shimura.Coefficients.instHasLimitsOfShapeSingleObjModuleCat_langlands_1` is now `instHasLimitsOfShapeSingleObjModuleCat_etaleAssociatedPullback` (kept by `Langlands.Shimura.Coefficients.ScalarRestriction`).
- `Langlands.Shimura.Coefficients.EtaleInverseImageAssociated`:
  - `Langlands.Shimura.Coefficients.instHasLimitsOfShapeSingleObjModuleCat_langlands_1` is now `instHasLimitsOfShapeSingleObjModuleCat_etaleInverseImageAssociated` (kept by `Langlands.Shimura.Coefficients.ScalarRestriction`).
- `Langlands.Shimura.Coefficients.TrivializationFromSplitting`:
  - `Langlands.Shimura.Coefficients.instHasLimitsOfShapeSingleObjModuleCat_langlands_1` is now `instHasLimitsOfShapeSingleObjModuleCat_trivializationFromSplitting` (kept by `Langlands.Shimura.Coefficients.ScalarRestriction`).
- `Langlands.Representation.LanglandsClassification.LeviInductionQuotient`:
  - `Langlands.Aubert.General.RepresentedParabolic.inductionQuotientAmbientTopology` is now `leviInductionQuotientAmbientTopology` (kept by `Langlands.Representation.Exponents.TemperedInductionQuotientNonvanishing`).
- `Langlands.Representation.CompactCoefficient.CompactGroupFormalDegreeProof`:
  - `Langlands.Renard.CompactRepresentation.finiteDimensional_of_compact_irreducible` is now `finiteDimensional_of_compact_smooth_irreducible` (kept by `Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof`).

The Library itself has meanwhile renamed the local instances of
`Langlands.Galois.Local.SeparableUnramifiedArithmeticStatement`, `SeparableValueArithmetic`,
`SeparableUnramifiedFiniteArithmetic`, `SeparableUnramifiedStatement` and of
`Langlands.ClassFieldTheory.Local.NYLL.SuppliedSpectralComparisonProof` and `FiniteInertiaField`
(integration efbffba), the topology of `Langlands.Correspondence.BaseReciprocityCoherence`
(7047367), and those of `Langlands.Automorphic.PlaceCompactAction` and `PlaceCompactCovariance`
(task 6c50b2fd-cb4a-47b3-8f5d-d464916d69fb). Worker 181 renamed the two Bernstein topologies of
`Langlands.Representation.CuspidalSupport` in candidate dfa664b0-ce94-4ff5-bc96-cceceef7b1a7. Those
files are left as the Library has them.

### How the names were checked

All checks ran in the Lean service. Private draft modules imported the Library modules in
chunks of about 2,000, chosen so that no chunk loads two different declarations of one name.
Each printed a 64-bit hash of every constant name its imported modules declare
(`constNames` and `extraConstNames` of `env.header.moduleData`). Comparing the hashes across
all modules found the shared names, and a second pass printed the full names behind them.
Constants that Lean realizes on demand in each module that needs them (`eq_N`, `eq_def`,
`congr_simp`, `match_N.splitter`) are identical copies that Lean accepts on import; they
are not renamed. This scan covered the 22,075 modules of Library e748734, and then the 176
modules that Library c6e8014 added or changed, with the modules importing them. For the
final state, the published names of the renamed modules were taken with each renamed
declaration replaced by its new name, and Lean hashed the new names. Every hash shared by
two modules then belonged to a realized constant.

Lean 4.34 names an unnamed instance with the first unused name among `B`, `B_1`, `B_2`, ...
for a base name `B`. Renaming an instance frees its old name, so later automatic names could
change. Among the renamed modules and the modules that import them, seven automatic instances
in four modules share a base name with a renamed instance. Re-deriving their names by this rule
reproduces their published names and gives the same names after the renames, because the
module that keeps each old name is among their imports. The 81 modules that Library 389dbc1
added and the eight it changed import none of the renamed modules, so the renames cannot change
their names. They were not scanned here, and Worker 181 is to rescan the published Library.
Each renamed module compiles in the Lean service.
