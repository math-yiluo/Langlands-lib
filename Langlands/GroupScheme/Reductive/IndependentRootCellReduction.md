# The arbitrary-field rank-one root cell from an independent geometric central cover

This internal supporting construction reduces the exact arbitrary-field root-cell proposition
to the explicit geometric premise `RankOneCentralCoverStatement`. It does not prove that
premise. In particular it is not an unconditional proof of `SplitRankOneRootCellStatement`.

## Result and retained premise

`splitRankOneRootCell_of_centralCover` proves

`RankOneCentralCoverStatement.{u} → SplitRankOneRootCellStatement.{u}`.

The conclusion is the existing Library proposition, with its original hypotheses and
arbitrary field and universe. The premise is an algebraically closed existence proposition:
a connected reductive group with a prescribed split maximal torus and nonempty, pairwise
integer-dependent actual roots has a central isogeny from `SL₂ × C`, for a split torus `C`,
and a compatible finite-flat-surjective isogeny from the standard product torus to the
prescribed torus. It does not assume a root datum, root reducedness, or root-space lines.

The entry definition `rootCellParametrizationsOfCentralCover` takes a proof of that global
geometric proposition and the original local cell data: an arbitrary field `k`, a connected
reductive `G`, a split maximal torus `i : T.toGrp ⟶ G`, a supplied actual root datum `P`,
pairwise integer dependence of actual roots, and a root index `r`. It returns a pair of
actual homomorphisms from `𝔾ₐ` to `G`, with
`RootCell.IsRootCell i (P.root r) (P.coroot r)` as its subtype property. This retains all
five root-cell clauses over every test scheme. No proof of the geometric premise is
included or claimed.

## Implemented reduction

First, `algClosedRankOneRootSupportLines_of_centralCover` works over an algebraically
closed field. The supplied datum identifies `P.root r` as an actual root, so the roots are
nonempty and the geometric cover hypothesis applies. Finiteness of the central isogeny
provides the affine and locally finite type instances of the source.
`eq_or_eq_neg_of_sl2_centralCover` (`Reductive/CentralCoverRootOpposition`) gives the actual
local support on `±P.root r`.
`RankOneCentralCover.rootLineOfCover_isogeny` supplies the two actual weight-space lines.
The negative root is supplied by `IsRootDatumOf.neg_mem_roots`. No reducedness is inferred
from the Mathlib root datum.

Second, `splitRankOneRootSupportLines_of_algClosed` (`Reductive/RankOneSupportLinesBaseChange`)
descends exactly that
support and those two lines to any split field. It extends the actual group, prescribed
torus, root datum and rank-one dependence to the algebraic closure. Actual character
pullback preserves and reflects root support; actual weight-space scalar extension reflects
the two line equivalences. Thus it proves the all-field structural interface from its
geometric counterpart.

Third, `splitRankOneRootCell_of_supportLines` applies
`LocalRankOneRootCell.exists_rootCell_of_support_lines` to the three local structural
conclusions. Its root-cell predicate gives, in order, the two conjugation formulas, the
open immersion, cell membership exactly when `1 + XY` is a unit, and the rank-one product
factorization. This is the exact existing `SplitRankOneRootCellStatement` conclusion.

Finally the entry definition uses the same descended structural data and the chosen pair
`LocalRankOneRootCell.parametrizationsOfSupportLines` to return actual parametrizations.
The source dependencies are included as complete paired modules; they retain their own
hypotheses. This construction does not turn their existence premises into
proved facts.

## Provenance and independence

This is an internal composition of actual-morphism constructions. Its source root lines
come from explicit SL₂ integral weights and matrix-entry injectivity; transfer uses actual
central-kernel and central-isogeny Lie maps. Its descent uses actual group-scheme and
weight-space base change. Its cell construction uses smooth affine dynamic coordinates,
centralizer representability, the dynamic open cell and the explicit Weyl relation. There
is no new translation from original literature and no cover-existence proof in this module.
The cover statement is proved separately as `rankOneCentralCover`
(`Reductive/RankOneCentralCoverProof`), and `IndependentGeometricReductivityProof` applies this
implication to it.

A terminal recursive type-and-value audit, including opaque values, reported:

| Declaration | Constants reached | Forbidden declarations reached |
| --- | ---: | ---: |
| `algClosedRankOneRootSupportLines_of_centralCover` | 46,417 | 0 |
| `splitRankOneRootCell_of_supportLines` | 111,496 | 0 |
| `splitRankOneRootCell_of_centralCover` | 111,958 | 0 |
| `rootCellParametrizationsOfCentralCover` | 111,962 | 0 |

The 21 cut points were `ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement`, their five corresponding proof declarations,
`splitRankOneRootCell`, `splitRootLieLine`, `prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`, `rootDatumExistence`,
`rootReducedness`, `reductiveGeometricReductivity`, `absoluteBruhatCovering`,
`steinbergBigCell`, and `isParabolicSubgroup_of_range_eq_dynamicParabolic`.

These measurements concern the conditional construction. The proof `rankOneCentralCover` of
`RankOneCentralCoverStatement` has its own independence audit, recorded in the Markdown of
`RankOneCentralCoverProof`. Exact entry-definition compilation and inspection succeeded, with
zero errors or warnings and only `propext`, `Classical.choice`, and `Quot.sound` as reported
axioms.
