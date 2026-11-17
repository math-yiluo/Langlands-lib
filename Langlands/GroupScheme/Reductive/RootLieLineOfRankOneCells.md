# Root Lie lines in proportional-root groups from supplied root cells

Worker 781, Task 7510. This is an internal derived supporting construction.
Both structural statements remain explicit inputs; this unit does not prove
`SplitRootLieLineStatement` unconditionally.

`RootCellLie.lineEquivOfRankOneDatum` constructs
`k ≃ₗ[k] weightSpace i α` for a root `α` of a split maximal torus
`i : T.toGrp ⟶ G` of a connected reductive group over an arbitrary field
`k : Type u`. It assumes a supplied actual root datum `P`, pairwise integral
linear dependence of every two roots, and
`SplitRankOneRootCellStatement.{u}`. No algebraic closure assumption is used.
The supplied datum is not required to be reduced by this construction.

The roots equality in `IsRootDatumOf i P` supplies an index `r` with
`P.root r = α`. The cell statement supplies its two additive maps and the
positive and negative equivariance laws, together with the open immersion.
`RootCellLie.lineEquiv` then trivializes the nonzero actual weight space.
The linked rank-one multiplication relation and the cell membership test
from the cell statement are unused. Existence witnesses are eliminated into
`Nonempty`, and classical choice selects the resulting linear equivalence.

`RootCellLie.lineEquivOfRankOneCells` chooses the datum from the explicit
input `RootDatumExistenceStatement.{u}` and applies the preceding construction.
Its root reducedness and finite indexing conclusions are unused. The result
is the proportional-root case needed by the general centralizer reduction.
The proof does not establish either structural input, and the Library's
current proofs of those inputs are not applied.

The provenance is internal composition of the published statement interfaces,
the earlier open-cell tangent construction and classical choice. There is no
external source transcription. Development compilation succeeded in pinned
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with zero errors or warnings
(diagnostic `8db96b66-55f4-4b9e-b47e-886d76b762fb`). The prerequisite pair is
`RootLieLineFromRootCell.lean` and `.md`.

## Type and value dependency audit

Worker 781 ran a private Lean environment traversal after importing these
modules. For each reached constant it traverses `ConstantInfo.type` and
`ConstantInfo.value? (allowOpaque := true)`, using `getUsedConstants` for both.
It records all names, and stops at excluded names to record witness paths.
The audit compares each final name component, so moving a declaration to a
namespace would not hide it. It checks these 24 names:

- `ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
  `RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
  `RankOnePositiveRootUniquenessStatement`, and their corresponding proofs
  `parabolicDynamic`, `regularCocharacterBorel`, `rankOneSolvableObstruction`,
  `rankOneBorelDynamic`, `rankOnePositiveRootUniqueness`;
- `splitRootLieLine`, `splitRankOneRootCell`,
  `rootLieLine_of_twoStructuralInputs`,
  `rootLieLine_of_dynamicCentralizerReductive`,
  `absoluteRootTangent_le_one_of_structuralInputs`,
  `rankOne_rootTangent_le_one_of_projectiveBorelInputs`,
  `prescribedBorelProjectiveCurveData`,
  `regularSignedCurveUnipotentDataOfIsConnectedReductive`;
- `rootDatumExistence`, `rootReducedness`, `reductiveGeometricReductivity`,
  `absoluteBruhatCovering`, `steinbergBigCell`,
  `isParabolicSubgroup_of_range_eq_dynamicParabolic`.

The terminal audit is diagnostic `111292dc-40a7-49c6-83ef-8498c6b3fe10` in the
same pinned environment. All counts include the root itself.

| Root declaration | All constants | Langlands constants | Excluded hits |
| --- | ---: | ---: | ---: |
| `RootCellLie.lineEquiv` | 38,718 | 803 | 0 |
| `RootCellLie.lineEquivOfRankOneCells` | 41,636 | 841 | 0 |
| `RootReducedness.map_weightSpace_torusFactor` | 28,638 | 803 | 0 |
| `dynamicCentralizerReductive` | 103,346 | 15,615 | 0 |

The positive control `VectorGroup.IsTorusEquivariant.represents_root` reaches
`splitRootLieLine` immediately, as expected. In particular, importing its
module for the independent lower-level differential-image lemma does not
make that excluded proof a dependency of this construction. This audit checks
named dependencies, including opaque theorem bodies; it does not substitute
for semantic review or for independently proving the two retained inputs.
