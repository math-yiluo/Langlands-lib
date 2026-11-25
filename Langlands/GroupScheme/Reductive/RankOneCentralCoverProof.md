# Proof of the rank-one SL₂ central cover

`Langlands.GroupScheme.rankOneCentralCover : RankOneCentralCoverStatement.{u}` proves the
published statement `Langlands.GroupScheme.RankOneCentralCoverStatement` (module
`Langlands/GroupScheme/Reductive/RankOneCentralCoverStatement.lean`) unchanged, for every
universe `u`.

## Structure of the proof

The theorem is `RankOneLocalCover.rankOneCentralCover_of_inputs` applied to two inputs.

1. **Root cell to cover.** `rankOneCentralCover_of_rootCell` (module
   `Reductive/RankOneCoverOfRootCell`, with `Reductive/RankOneCoverTorus`,
   `Reductive/SpecialLinearTensorCell` and `UnitLocusOpenImmersion`) turns a root cell
   `RootCell.IsRootCell i α αv xp xm` with `⟨α, αv⟩ = 2` into the split torus `C`, the central
   isogeny `SL₂ × C → G` and the torus isogeny `D × C → T` of the target. It is fed in through
   the proposition `RankOneLocalCover.RootCellCoverInput`.
2. **Local line crux.** `RankOneLocalCover.localLineCrux` (module `Reductive/RankOneFlagCrux`)
   proves `RankOneLocalCover.LocalLineCrux`. For every root `α` there is a cocharacter `ν`
   positive on `α` such that `α` (resp. `-α`) is the only root positive (resp. negative) on
   `ν`, and the weight spaces of `±α` are lines.

`rankOneCentralCover_of_inputs` (module `Reductive/RankOneLocalCover`) combines them through
`RankOneLocalAssembly.exists_isRootCell`. That theorem builds the root cell from the crux: the
Weyl point, the open cell `U(-α) T U(α)`, and the coroot with `⟨α, αv⟩ = 2`
(`RankOneLocalCell`, `RankOneLocalCoroot`, `RankOneLocalRootCell`).

## Route of the crux (route A)

Route A has the following steps:
- **Ordinary Borel and proper quotient.** A Borel `B` containing the maximal torus, the proper
  quotient `X = G/B` (`IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint`), and a
  nonidentity Weyl point `n` (`RankOneFlagSetup`).
- **Base point.** A point fixed by `T · U(-ν)`, for `ν` or `-ν`, from the solvable fixed-point
  theorem and torus limit induction (`RankOneFlagCrux.exists_coreData`). Here `ν = ν₀ - w ν₀` is
  the normalizer-symmetrized cocharacter.
- **Dimension bound.** Open cells `U(ν) · x₀` and `U(-ν) · x₁`, Białynicki-Birula limits, the
  classification of the torus-fixed points, and a Chevalley map from the cell to an affine
  scheme (`RankOneFlagCell`, `RankOneFlagDimension`). These give the Bruhat decomposition
  `X = cell ⊔ {x₁}`. A Hartogs extension at the factorial point `x₁` (the purity property of
  factorial local rings) then gives `topologicalKrullDim X ≤ 1`, and also `U(ν) ⊄ B`.
- **Kernel step.** The general curve lemmas, see the next section.

## The kernel step and the general curve lemmas

The kernel step (`RankOneFlag.CoreData.finrank_tangent_le_one` in `RankOneFlagCrux`) uses the
general Library curve construction `HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` and,
through it, `HomogeneousQuotient.unipotent_dimension_le_one` (module
`Dynamic/HomogeneousCurveUnipotentProof`). Both are general statements about a closed solvable
subgroup `B` of a pseudo-reductive group whose homogeneous quotient is a curve, and a dynamic
unipotent `U(ν)` not contained in `B`. Neither mentions an excluded statement. The third curve
lemma, `HomogeneousQuotient.positive_roots_eq_of_noncontained_unipotent_on_curve`, is not called.
Positive-root uniqueness is instead taken from the tangent bound by
`RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one`.

Here the curve lemmas are applied to the ordinary flag variety `G/B`. Their two hypotheses are
proved in this development:
- `dim G/B ≤ 1` is `CoreData.topologicalKrullDim_le_one`, obtained by Białynicki-Birula limits,
  the fixed-point classification and the Hartogs/purity argument above;
- `U(ν) ⊄ B` is `CoreData.not_unipotent_le`.

Neither comes from the prescribed-Borel argument of the excluded projective-Borel route:
`prescribedBorelProjectiveCurveData`, `ProjectiveTorusFixedPointDimension`,
`positive_roots_eq_of_rankOne_curve_quotient` and `signedCurveUnipotentData` are neither called
nor reached.

The curve construction handles `U(ν) ∩ B` itself. It passes to the smooth connected
representative, which is normal in the unipotent group by its codimension-one argument
(`Unipotent/CodimensionOneNormality`). The tangent bound then gives the root lines through
`RelativeRoot.weightSpace_le_tangentSubmodule_unipotent`. The symmetric bound for `-ν` comes
from `IsConnectedReductive.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg`.

How `Q = U(ν) ∩ B` enters the dimension bound: the Chevalley map on the cell uses the stabilizer
subgroup scheme `Q` of `x₀` in `U(ν)` only through Chevalley's theorem. That theorem gives an
affine orbit map whose fibres are exactly the `Q`-cosets. No smoothness, reducedness or
normality of `Q` enters. The dimension bound uses only that this map is injective on rational
points.

General lemmas proved for this development: `AlgebraicGeometry/FactorialHartogsExtension`,
`HartogsAffineConstancy`, `KrullDimensionChain`, `ClosedRationalPoints`,
`GroupScheme/Dynamic/SplitTorusLimitInduction`, `GmOrbitInversion`, `TwoSidedConstancy` and
`GroupScheme/SchemeActionTranslation`.

## Independence and mechanical check

The proof uses none of the excluded statements or proofs:
- `ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
  `RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
  `RankOnePositiveRootUniquenessStatement`, nor their proofs;
- the current `rootDatumExistence`, `rootReducedness`, `reductiveGeometricReductivity` and
  `ReductiveLinearQuotientAffineStatement` proofs;
- properness of any quotient `G/P(ν)` (`DynamicQuotientProperStatement`);
- the projective-Borel route (`ProjectiveTorusFixedPointDimension`,
  `prescribedBorelProjectiveCurveData`, `regularSignedCurveUnipotentDataOfIsConnectedReductive`,
  `rankOne_rootTangent_le_one_of_projectiveBorelInputs`,
  `positive_roots_eq_of_rankOne_curve_quotient`);
- no circular dependence on the target. The proof does not use a supplied central cover
  (`RankOneCentralCoverStatement` as a hypothesis), and it does not use any published consumer
  of the cover, such as the cover-to-root-cell and cover-to-root-line results
  (`splitRankOneRootCell_of_centralCover`, `algClosedRankOneRootSupportLines_of_centralCover`).

The target does occur in one place besides the final theorem. It is the result type of the
directly called assembly `RankOneLocalCover.rankOneCentralCover_of_inputs`, whose proof
derives the target conclusion from its two inputs (`RootCellCoverInput` and `LocalLineCrux`).
This is not circular: both inputs are proved independently, by
`rankOneCentralCover_of_rootCell` and `localLineCrux`.

The mechanical check is the type-and-value closure scan used for the inputs, extended to the final
proof. It includes opaque values. It removes the target
statement from the root's type, and it traverses the value of
`RankOneLocalCover.rankOneCentralCover_of_inputs` instead of stopping at its result type. Every
other occurrence of `RankOneCentralCoverStatement` in the closure would count as a hit. The final
scan visited 115210 constants, 20999 of them Library
constants from 1682 modules, and found none of the excluded declarations.

The curve lemmas are reached only along the chain `RankOneFlag.CoreData.finrank_tangent_le_one` →
`HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` →
`HomogeneousQuotient.unipotent_dimension_le_one` →
`SchemeAction.unipotent_dimension_le_one_of_dominant_orbit` →
`SchemeAction.range_eq_bot_of_unipotent_kernel`, together with the structures
`HomogeneousQuotient.CurveUnipotentData` and `HomogeneousQuotient.curveOrbitData`.

Other auxiliary Library lemmas of the kernel and line steps are:
- `HomogeneousQuotient.lie_dimension_le_add_one_of_dimension_le_one` and
  `HomogeneousQuotient.smooth_reduced_irreducible_quotient`;
- `RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one` and
  `RelativeRoot.weightSpace_le_tangentSubmodule_unipotent`;
- `IsConnectedReductive.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg`.

The scanner, the exclusion list, the Library modules and all Library constants reached are in
the published notes `notes/group-schemes/rank-one-central-cover-dependency-audit.md` and
`notes/group-schemes/rank-one-central-cover-dependency-constants.md`. An independent
audit of this proof reached the same conclusions, including the chain above.
