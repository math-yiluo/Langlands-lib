# Splitting a segment induction into its first factor and its tail

This internal helper module is the fifth of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`. Let `A` be
a smooth representation of `GL_r(F)`, `r > 0`, and let `m = k + 2`. The module
splits the two published segment inductions of length `m` into a first factor
and a tail of length `k + 1`, as rank-cast binary normalized products:

- the decreasing induction `ν^(k+1) A × ν^k A × ⋯ × A` is isomorphic to
  `ν^(k+1) A × (ν^k A × ⋯ × A)` (`nonempty_iso_segmentInducedDown_split`);
- the increasing induction `A × νA × ⋯ × ν^(k+1) A` is isomorphic to
  `A × (νA × ⋯ × ν^(k+1) A)`, where the tail is the increasing induction of
  length `k + 1` of `νA` (`nonempty_iso_segmentInduced_split`).

It also twists supercuspidal representatives. All declarations live in the
namespace `Langlands.Classification.SegmentHeadSupport`.

## Rank casts

`rankCast_rankCast_obj` composes two rank casts. `binary_rankCast_right_obj`
moves a rank cast of the second factor of a binary product outside the
product. `binary_obj_congr` rewrites the factors of a binary product along
equations. Each is proved by `subst` on the equations.

## Twists

- `twistIsoOfEq`: twists of a smooth representation by equal characters are
  isomorphic. The same one-line construction occurs in the Library module
  `SegmentSocleJacquetReduction`. That module is not imported.
- `twistRep s A` is the published supercuspidal twist
  `SupercuspidalRep.twist` of a representative `A` by the character
  `|det|^s` (`T.determinantPowerCharacter r s`). `twistRep_obj` records that
  its underlying representation is the published segment factor
  `T.segmentFactor A s`.
- `isRepresentedBy_twistRep`: if `A` represents the cuspidal datum `ρ`, then
  `twistRep s A` represents `ρ.twist s`. This holds by definition of the
  published twist of cuspidal data,
  `T.supercuspidalClassRealPowerTwist`.
- `segmentFactorTwistIso`: `ν^j (ν A) ≅ ν^(j+1) A`. It combines the published
  `SmoothRep.twistTwistIso` with `realPowerCharacter_add`.

## Splits

`uniform_tailRank`, `uniform_tailShape` and `uniform_split_rank` compute the
tail rank `(k + 1) r` and the tail shape of the uniform block shape
`BlockShape.uniform m r`. `headTail_uniform_obj` combines the published
head/tail shape API of `HeadTailProductInduction` with the shape equations of
`SegmentHeadSupportCons`. It writes product induction on the head/tail shape
of the uniform shape as the rank cast of the binary product of the first
factor with product induction on `BlockShape.uniform (k + 1) r`.

- `nonempty_iso_segmentInducedDown_split` composes the published
  `T.headTailProductInductionIso` with this equation. The factors of the
  published `T.segmentFactorsDown A m` are `ν^(m-1-i) A`. So the first factor
  is `ν^(k+1) A`, and the tail factors are those of
  `T.segmentFactorsDown A (k + 1)`.
- `nonempty_iso_segmentInduced_split` does the same for the published
  `T.segmentFactors A m`, whose factors are `ν^i A`. The first factor is
  `ν^0 A`, and the tail factors `ν^(j+1) A` are identified with the factors
  `ν^j (νA)` of `T.segmentInduced (νA) (k + 1)` by `segmentFactorTwistIso`.

## Provenance and inputs

All statements are internal lemmas about the published definitions of segment
inductions (`Classification.Segments`), of normalized product induction and of
the head/tail decomposition of a block shape. Normalized induction in stages
for the head/tail split is the published `headTailProductInductionIso`. No
assertion from the literature is transcribed.

Direct import: `Langlands.Representation.Classification.SegmentHeadSupportCons`.
The complete closure audit is in
`SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
