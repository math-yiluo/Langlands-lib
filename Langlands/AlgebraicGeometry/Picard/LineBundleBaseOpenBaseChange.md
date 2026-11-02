# The base open classifying line-bundle base changes

This is an internal derivation from `LineBundleLocus`,
`RankOneCartesianBaseChange`, the universal property of open immersions,
and Mathlib's description of the image of a subset under a cartesian
square of schemes.

Consider a cartesian square with maps `a : P → Y`, `p : P → T`,
`f : Y → S`, and `g : T → S`. Assume `f` is universally closed and
locally of finite presentation, and `M` is a locally finitely presented
module sheaf on `Y` that is relatively flat over `S`.

The lemma `isLocallyFreeRankOne_pullback_iff_mem_baseOpen` states that
the ordinary pullback of `M` to `P` is locally free of rank one if and
only if every point of `T` maps into `rankOneBaseOpen f M`.
For the forward direction, every pair of points `y ∈ Y`, `t ∈ T` with
the same image in `S` lifts to a point of the scheme pullback. The
rank-one locus base-change equality then shows that `y` is in the
original rank-one locus. The reverse direction uses the existing
pullback of local trivializations above the base open.

If `p` is also universally closed, the lemma
`rankOneBaseOpen_pullback_of_isPullback` identifies the base open formed
on `T` with the inverse image of the base open on `S`. Universal
closedness of `p` follows from that of `f` in a cartesian square;
it is supplied explicitly to allow the existing base-open construction
to be used in the statement. The proof rewrites the rank-one loci using
`RankOneCartesianBaseChange` and applies the image-preimage identity for
scheme pullbacks to their complements.

The construction `rankOneBaseOpenLift` produces an actual scheme morphism
from `T` to this open subscheme whenever the pulled-back module is a line
bundle. Its composite with the open inclusion is exactly `g`, and
`rankOneBaseOpenLift_uniq` proves uniqueness.

All tests are actual schemes in arbitrary universe `u`, including empty,
nonreduced and non-quasi-compact schemes. No flatness condition is imposed
on `g`, and no noetherian hypothesis is used. This unit proves the stated
open-factorization criterion; stack-level representations and the Picard
atlas theorem remain further obligations.
