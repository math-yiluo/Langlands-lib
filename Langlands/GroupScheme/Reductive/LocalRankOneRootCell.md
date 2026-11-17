# Rank-one root cells from local root support and root-space lines

Authors: Worker 777 and Worker 785 (interface coordination).

This internal supporting unit constructs root-cell parametrizations from explicit local
structural data over an arbitrary field. It does not prove the existence of that structural
data, and does not prove `SplitRankOneRootCellStatement` without further input.

## Mathematical interface

Work over a field `k : Type u`. Let `G` be a connected reductive group, let
`i : T.toGrp ⟶ G` be a split maximal torus, and let
`P : RootDatum J (characterLattice T) (cocharacterLattice T)` satisfy
`IsRootDatumOf i P`. Assume any two actual roots in `roots i` are linearly dependent
over `ℤ`. Fix `r : J`, and write `α = P.root r` and `h = P.coroot r`.

`LocalRankOneRootCell.exists_rootCell_of_support_lines` takes three extra local hypotheses:

- Every actual root `β ∈ roots i` equals `α` or `-α`.
- There is a linear equivalence `k ≃ₗ[k] weightSpace i α`.
- There is a linear equivalence `k ≃ₗ[k] weightSpace i (-α)`.

It concludes that there are homomorphisms `xp xm : 𝔾ₐ ⟶ G` satisfying
`RootCell.IsRootCell i α h xp xm`. This predicate includes torus conjugation through `α`
and `-α`, the open immersion `xm × i × xp`, cell membership exactly when `1 + XY` is a
unit over every test scheme, and the factorization
`xp(X) xm(Y) = xm(u⁻¹Y) h(u) xp(u⁻¹X)` for `u = 1 + XY`.

The definition `LocalRankOneRootCell.parametrizationsOfSupportLines` chooses a pair of those
homomorphisms and retains `RootCell.IsRootCell` as its subtype property. This is the entry
declaration. The root datum is supplied, and its reducedness is not assumed or inferred.

## Implemented construction

The preliminary theorem `exists_rootGroup_of_positiveSupport` needs only a root `α`, a
cocharacter `ν` with positive pairing, uniqueness of the actual roots pairing positively
with `ν`, and a supplied line `weightSpace i α`. It does not need a global root-uniqueness
or line theorem.

The smooth affine dynamic unipotent group `Standard.unipotentScheme i ν ∅` has free
positive-weight coordinates and a triangular multiplication law, by
`TorusUnipotence.exists_positiveWeight_coordinates` and `exists_triangular_mul`. The
coordinate multiplicity theorem and the comparison with actual adjoint weights show that
every coordinate weight is an actual positive root. Local positive support makes all those
weights `α`; the supplied root line then makes the number of coordinates one. The
triangular correction to the first coordinate has no variables, and its value at the
identity vanishes. The coordinate is therefore additive. The clean affine-coordinate
helpers in `RankOneCellData` extend its evaluation from affine points to every test scheme.
`RelativeRoot.vectorGroupIso` gives an additive-group parametrization; its eigenfunction
law gives the required torus conjugation.

For the main construction the root datum gives the pairing `⟨α, h⟩ = 2` and the negative
root. The local support hypothesis makes `α` the only positive root for `h`, and `-α` the
only positive root for `-h`. Apply the preliminary construction twice.
`rankOne_centralizer_isRepresentedBy`, discharged with `dynamicCentralizerReductive`,
identifies the dynamic centralizer with `T`, using only the rank-one dependence hypothesis.
`Dynamic.isOpenImmersion_tripleCellMultiplication` gives the open cell from the three
representatives.

The supplied root datum realizes its reflection by a rational normalizer point.
`RankOneRootCellRelation.exists_sq_eq_of_isNormalizingPoint` places its square in the
torus. These data form `RankOneRootCellRelation.WeylData`. Its `isRootCell` theorem
rescales the negative parametrization by a nonzero scalar and supplies cell membership
and the product relation over all test schemes. Finally the entry definition chooses the
two witnesses using classical choice.

## Provenance and independence

This is an internal conditional construction derived from the clean affine-coordinate,
dynamic-centralizer, dynamic-cell and explicit Weyl-relation helpers described above.
The coordinate part adapts the implemented construction in `RankOneCellData`; it replaces
its global structural inputs with the displayed local hypotheses. No proof of those
hypotheses is asserted or copied here. The geometric existence theorem in the original
task remains open. The target's literature context is documented in
`SplitRankOneRootCellStatement.md`; this unit makes no additional source translation.

The development audit traversed constants used in both types and values, including opaque
values, recursively. Terminal check `e1b0a36c-8aa8-4b3c-9cc0-fbf9285549c2` reported:

| Declaration | Constants reached | Forbidden declarations reached |
| --- | ---: | ---: |
| `exists_rootGroup_of_positiveSupport` | 58,228 | 0 |
| `exists_rootCell_of_support_lines` | 111,482 | 0 |
| `parametrizationsOfSupportLines` | 111,490 | 0 |

The 21 cut points were the five excluded statement declarations
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`, and
`RankOnePositiveRootUniquenessStatement`; their five corresponding proof declarations;
and `splitRankOneRootCell`, `splitRootLieLine`, `prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`, `rootDatumExistence`,
`rootReducedness`, `reductiveGeometricReductivity`, `absoluteBruhatCovering`,
`steinbergBigCell`, and `isParabolicSubgroup_of_range_eq_dynamicParabolic`.

The module imports published helper declarations from files that also contain excluded
results. Import reachability is broader than type-and-value reachability. The imported
excluded proof declarations are not invoked. Semantic independence still requires
independent review of the mathematical route. The development scanner remains private
and is not part of this submission.

Compilation and exact inspection of the entry definition succeeded in terminal check
`5852d49e-ed49-498f-a989-e0df8b3a9ae8`, with zero errors or warnings. The only reported
axioms were `propext`, `Classical.choice`, and `Quot.sound`.
