# Actual root-space lines from a supplied standard rank-one cover

Author: Worker 777.

This internal supporting unit constructs actual root-space lines from explicit matrix data
and a supplied compatible central cover. It does not construct a cover or prove the original
rank-one root-cell statement. All fields and schemes retain arbitrary universe `u`.

## Interface

Let `k` be an arbitrary field, let `G` be an affine, locally finite type group scheme over
`Spec k`, and let `T` and `C` be commutative group schemes that are split tori. Write
`D = splitTorus.commGroupScheme (Spec k) (ULift (Fin 1))`,
`SL = SpecialLinear.groupScheme (Fin 2) k`, and let `d : D.toGrp ⟶ SL` be the standard
diagonal-torus homomorphism. The interface also explicitly installs the affine and locally
finite type instances for `SL × C`.

The entry definition `RankOneCentralCover.rootLineOfCover_isogeny` takes:

- an actual group-scheme homomorphism `i : T.toGrp ⟶ G`;
- a central isogeny `q : SL × C ⟶ G`, in the Library's sense, including centrality of the
  full scheme-theoretic kernel;
- a finite, flat, surjective torus isogeny `t : D × C ⟶ T`;
- the equality `(d × id_C) ≫ q = groupHom t ≫ i`;
- an actual root `χ ∈ roots i`.

It constructs `k ≃ₗ[k] weightSpace i χ`. Neither `i` being maximal, reductivity of `G`,
root-datum existence, reducedness, nor algebraic closedness is required. The supplied cover
is substantial input. The more general `rootLineOfCover` replaces the torus-isogeny
hypothesis by injectivity of character pullback along `t`.

## Explicit SL₂ calculation

In `SpecialLinear.FinSucc`, `eq_pair_of_weightCoord_sub_eq_one` checks that the nonzero
integral difference of two weights of the diagonal torus determines its ordered pair of
matrix indices. This is a finite calculation on `Fin 2`, using the already defined
integral characters, so it does not identify weights merely by their derivatives.

`rootEntry χ p q` evaluates the actual Lie matrix at `(p,q)`. The published
`mem_weightSpace_diagonalTorus_iff_support` says every nonzero entry of a vector of weight
`χ` has integral weight `χ`. Thus, for a root with coordinates `w(p)-w(q)`, every entry
other than `(p,q)` vanishes. Evaluation at this entry is injective
(`rootEntry_injective`), using injectivity of the actual Lie-matrix map. Consequently the
root space has dimension at most one. It is nonzero by the definition of an actual root,
so its dimension is exactly one (`finrank_weightSpace_eq_one`). The definition `rootLine`
chooses the resulting linear equivalence with `k`.

This calculation uses actual SL₂ dual-number Lie coordinates and the integral character
lattice in every characteristic. It uses no general root-line theorem.

## Product and cover transfer

`finrank_eq_one_of_centralKernelMap` is a general helper with an arbitrary affine locally
finite type source `H`. Suppose `p : H ⟶ SL` has central full kernel, a split torus `S`
acts on `H` through `j`, and `j ≫ p` is the diagonal-torus action pulled back along
`t : S ⟶ D` with injective character pullback. The actual differential is injective on
every nonzero source weight, by
`Lie.weightSpaceMap_injective_of_central_kernel`. The published
`Lie.weightSpaceCompEquiv` identifies the corresponding target weight with the original
SL₂ root space. The source therefore has dimension at most one; a supplied actual source
root makes it nonzero. `rootLineOfCentralKernelMap` chooses its line.

For `H = SL × C`, take the first projection. Its full kernel is central because `C` is
commutative (`isCentral_kernel_fst_comm`). Character pullback by the first torus projection
is injective because that projection has a section (`prodFst_character_injective`). The
published `exists_root_of_mem_roots_sl2_tensor` says every actual product root is pulled
back from an actual SL₂ root. The preceding helper yields `productRootLine`.

For the final transfer, a target root remains nonzero under injective character pullback.
The compatibility equality and `mem_roots_comp_iff` make its pullback a root for the
source torus acting through `q`; `roots_comp_eq_of_centralIsogeny` makes it an actual root
of the source. Its source space is the line just constructed. The actual differential
`Lie.nonzeroWeightSpaceEquivOfCentralIsogeny` identifies that space with the corresponding
target weight space for the source-torus action, and the injective character-pullback
comparison identifies the latter with `weightSpace i χ`. Composing gives `rootLineOfCover`.
Finally flat surjectivity of the supplied torus isogeny makes its scheme map an
epimorphism, giving injective character pullback and the entry construction.

The proof permits inseparable central isogenies and nonreduced kernels. It uses the actual
nonzero-weight differential equivalence, which is already proved without a separability
or smooth-kernel hypothesis.

## Provenance and dependency audit

This is an internal deduction from published explicit SL₂ matrix coordinates, actual
central-kernel Lie maps, split-torus weight comparison, and the nonzero-weight equivalence
for a central isogeny. It makes no new translation from original literature. Its geometric
existence premise is deliberately retained.

A recursive audit follows all constants in both types and values, including opaque values.
Terminal check `a0166875-298f-47b9-99b9-640e1506cdf5` reported:

| Declaration | Constants reached | Forbidden declarations reached |
| --- | ---: | ---: |
| `SpecialLinear.FinSucc.rootLine` | 41,589 | 0 |
| `RankOneCentralCover.rootLineOfCentralKernelMap` | 41,972 | 0 |
| `RankOneCentralCover.productRootLine` | 42,012 | 0 |
| `RankOneCentralCover.rootLineOfCover` | 46,268 | 0 |
| `RankOneCentralCover.rootLineOfCover_isogeny` | 46,280 | 0 |

The 21 cut points were `ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement`, their five corresponding proof declarations,
`splitRankOneRootCell`, `splitRootLieLine`, `prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`, `rootDatumExistence`,
`rootReducedness`, `reductiveGeometricReductivity`, `absoluteBruhatCovering`,
`steinbergBigCell`, and `isParabolicSubgroup_of_range_eq_dynamicParabolic`.
The development scanner remains private and is not submitted. Semantic independence
remains subject to independent review.

Exact compilation and inspection of the entry definition succeeded in terminal check
`c7efc01f-1cb6-4a2c-a329-d4e1e326372e`, with zero errors or warnings. It reports only
`propext`, `Classical.choice`, and `Quot.sound` as axioms.
