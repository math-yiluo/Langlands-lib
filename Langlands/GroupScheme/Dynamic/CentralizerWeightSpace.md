# Weight spaces in actual cocharacter centralizers

This internal construction identifies character weight spaces under an actual
cocharacter centralizer inclusion. It is a supporting step for the reduction of
the root-line statement `SplitRootLieLineStatement` to proportional-root
centralizers (`Reductive.RootLieLineRankOneReduction`), rather than an
unconditional proof of the root-line statement.

`Lie.weightSpaceEquivOfLeRange` works over any commutative base ring `R`.
Let `s : M ⟶ G` be a group-scheme homomorphism whose underlying morphism is
monomorphic, and let `t : T.toGrp ⟶ M` be a homomorphism from a commutative
group scheme. Both `M` and `G` have affine structure morphisms. If the ambient
weight space for a character `χ` lies in the image of the differential of `s`,
the restricted differential gives an `R`-linear equivalence from
`weightSpace t χ` to `weightSpace (t ≫ s) χ`. The forward map is the existing
`Lie.weightSpaceMap`. Monomorphy gives injectivity, and the range assumption
gives a lift of each ambient vector. The existing
`lieKernelHomLinear_mem_weightSpace_iff` shows that each lift has the required
intrinsic weight. The companion coercion lemma records the forward map.

`Dynamic.weightSpaceEquiv_torusFactor` specializes this construction over any
field `k : Type u`. The ambient group has an affine, locally finite type
structure morphism. The group `L` is affine, and the given inclusion `j`
represents the dynamic centralizer of `ζ ≫ i`, where `ζ` is a cocharacter of
the acting commutative group scheme. For every character `χ` with
`latticePairing T χ ζ = 0`, it identifies the weight space in `L` for the
canonical `Dynamic.torusFactor` with the ambient weight space for `i`.
The range hypothesis is exactly
`RootReducedness.weightSpace_le_range_centralizer`; the equality
`Dynamic.torusFactor_comp` identifies the ambient action.
`Dynamic.nonempty_line_torusFactor_iff` then transports a linear
trivialization in either direction. The final identification of the ambient
action uses `LinearEquiv.ofEq` for the equality of the two weight submodules.

The characters need not be roots, and the construction assumes neither
reductivity nor algebraic closedness. It also does not construct a rank-one
centralizer, a root datum or a root cell. Its provenance is the elementary
restriction-and-reflection argument above, implemented with published
differential and centralizer APIs.

## Dependency audit

A private Lean command was checked against the module. For each public
declaration it traversed every constant in the declaration's type and value,
recursively, including opaque values with
`ConstantInfo.value? (allowOpaque := true)`. The resulting check reported no
missing constants and no forbidden dependencies:

| Declaration suffix | Total constants | `Langlands` constants |
| --- | ---: | ---: |
| `weightSpaceEquivOfLeRange` | 24,144 | 216 |
| `weightSpaceEquivOfLeRange_coe` | 24,145 | 217 |
| `weightSpaceEquiv_torusFactor` | 28,682 | 839 |
| `nonempty_line_torusFactor_iff` | 28,683 | 840 |

The forbidden list consisted of the five statement names
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement`; their respective proof names
`parabolicDynamic`, `regularCocharacterBorel`, `rankOneSolvableObstruction`,
`rankOneBorelDynamic`, `rankOnePositiveRootUniqueness`; the existing
`splitRootLieLine` and `splitRankOneRootCell`; the chain
`rootLieLine_of_twoStructuralInputs`,
`rootLieLine_of_dynamicCentralizerReductive`,
`absoluteRootTangent_le_one_of_structuralInputs`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`,
`prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`; and
`rootDatumExistence`, `rootReducedness`, `reductiveGeometricReductivity`,
`absoluteBruhatCovering`, `steinbergBigCell`,
`isParabolicSubgroup_of_range_eq_dynamicParabolic`.
Matching used the entire final name component, under any namespace.

This is a declaration-dependency audit. It does not establish that future
arguments supplying these constructions' hypotheses are independent.
Mathematically, the construction only restricts an injective differential and
lifts vectors from its range; it does not reconstruct a Borel argument.
