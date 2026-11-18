# Split root lines from a supplied geometric rank-one central cover

Author: Worker 781.

This internal supporting construction reduces the exact arbitrary-field
`SplitRootLieLineStatement.{u}` to the single explicit premise
`RankOneCentralCoverStatement.{u}`. It retains arbitrary universe `u`.
The geometric central-cover existence theorem remains unproved here.

## Actual rank-one line over the original field

`RankOneCentralCover.nonempty_rootLine_of_rankOneCover` assumes an arbitrary
field `k`, a connected reductive group `G`, a prescribed split maximal torus
`i : T.toGrp ⟶ G`, pairwise integer dependence of the actual roots, and a
specified actual root `chi`. It also assumes the global geometric cover
proposition above. It concludes
`Nonempty (k ≃ₗ[k] weightSpace i chi)`.

The proof extends the actual group, prescribed torus, torus homomorphism,
and character to `AlgebraicClosure k` in the same universe. Published
base-change results preserve connected reductivity and maximality, actual
root membership, and pairwise integer dependence. The specified root makes
the geometric root set nonempty, so the supplied cover proposition applies.
It supplies `SL₂ × C`, its actual central isogeny to the base-changed
group, a finite-flat-surjective isogeny to the prescribed torus, and their
compatibility square.

The published `RankOneCentralCover.rootLineOfCover_isogeny` gives the
base-changed root-space line from explicit integral SL₂ matrix weights and
the actual nonzero-weight differential of the supplied central isogeny.
The published `weightSpace_line_baseChange_iff` reflects that line to the
original field using actual weight-space scalar extension and preservation
of finite dimension.

The entry definition `RankOneCentralCover.rootLineOfRankOneCover` chooses
the resulting linear equivalence with the original field. It does not
assert that a particular linear coordinate on the geometric line descends.
There is no perfectness, characteristic, separability, or smooth-kernel
premise.

## General-rank conclusion

`splitRootLieLine_of_centralCover` applies the published
`splitRootLieLine_of_rankOne` to `dynamicCentralizerReductive` and the
rank-one assertion just proved. The generic reduction chooses a lattice
cocharacter whose actual centralizer contains the prescribed root and has
pairwise dependent roots, applies the rank-one assertion there, and
transports its line through the actual centralizer differential.

This proves the unchanged `SplitRootLieLineStatement.{u}` with
`RankOneCentralCoverStatement.{u}` as an explicit extra premise. It does
not provide an unconditional proof of the target or completion of the
host task.

## Provenance

This is an internal composition of published constructions, rather than
a new translation from original literature. It uses the explicit SL₂
line calculation and central-cover transfer of
`Reductive/RankOneCentralCoverLines`, actual-root and weight-space
base-change comparisons, maximal-torus base change, and the generic
centralizer line reduction of `Reductive/RootLieLineRankOneReduction`.
It supplies no root datum or root-cell existence argument.

## Dependency audit

Terminal check `4eed66da-3339-415e-a44e-4f6cf23c316f` compiled this module,
inspected the entry definition, and ran a private recursive dependency
scanner in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, over Library
base `18c5dd82d119bef479b69de264324b22fe6f8d36`. The definition has the
single arbitrary universe parameter `u`. The scanner follows every reached
constant's type and value, including opaque values, and fails on forbidden
or missing constants. It reported:

| Declaration suffix | Total constants | `Langlands` constants |
| --- | ---: | ---: |
| `RankOneCentralCover.rootLineOfCover_isogeny` | 46,280 | 999 |
| `RankOneCentralCover.nonempty_rootLine_of_rankOneCover` | 109,492 | 17,484 |
| `RankOneCentralCover.rootLineOfRankOneCover` | 109,498 | 17,490 |
| `splitRootLieLine_of_centralCover` | 111,163 | 18,854 |

All four closures have zero forbidden hits and zero missing constants.
Both the entry definition and the general-rank theorem use only the axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The scanner checks all 24 named exclusions of Task 7510:
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement`, their five respective proof names
`parabolicDynamic`, `regularCocharacterBorel`,
`rankOneSolvableObstruction`, `rankOneBorelDynamic`,
`rankOnePositiveRootUniqueness`, and
`splitRootLieLine`, `splitRankOneRootCell`,
`rootLieLine_of_twoStructuralInputs`,
`rootLieLine_of_dynamicCentralizerReductive`,
`absoluteRootTangent_le_one_of_structuralInputs`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`,
`prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rootDatumExistence`, `rootReducedness`,
`reductiveGeometricReductivity`, `absoluteBruhatCovering`,
`steinbergBigCell`, and
`isParabolicSubgroup_of_range_eq_dynamicParabolic`.

To guard against cycles with downstream work, it additionally checks
`SplitSimplyConnectedCorootSpanStatement`,
`splitSimplyConnectedCorootSpan`,
`algClosedGraphProjectionIsomorphisms`,
`splitCommonTorusIsomorphism`, and `splitCentralIsogenyExistence`.
The module `SimplyConnected.SplitCorootSpanLineReduction` is absent from
the import graph. Four further checks verify that the direct construction
avoids the separate root-datum and root-cell route:
`RootDatumExistenceStatement`, `SplitRankOneRootCellStatement`,
`rootDatumExistence_of_rankOneReducedness`, and
`splitRankOneRootCell_of_centralCover`.

Matching uses the entire final name component under any namespace.
The scanner and its diagnostics remain private development evidence.
The proof itself uses actual scalar extension, matrix root spaces, the
supplied cover, and centralizer transport. Independence of a future
unconditional application still depends on the proof supplied for
`RankOneCentralCoverStatement`.
