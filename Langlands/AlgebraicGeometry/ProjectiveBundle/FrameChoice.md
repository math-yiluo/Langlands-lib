# Independence of the chosen local frames

Let an actual module sheaf `M` on a scheme be locally free of rank
`n + 1`. Keep the cover by all opens carrying a frame of this rank.
`FrameFamily M n` allows any choice of an actual frame on each of these
opens. It supplies no additional local existence assumption: the
fixed-rank local-freeness hypothesis already ensures the cover.

`familyCocycle` forms the strict dual-frame cocycle for any such family,
and `familyBundle` is its actual glued projective scheme. Both use the
same construction and coefficient comparison as `frameBundle`.

For two frame families, `familyChange` uses the actual change between
their dual frames on each open. Restriction of frame changes and their
composition law prove the compatibility equation between the two
cocycles. Applying `CoordinateCocycle.Change.schemeIso` constructs
`frameChoiceIso`, an actual scheme isomorphism. Its chart equation is
the specified dual-frame coordinate action, and it commutes with the
structure morphisms to the base.

The comparison with the same family is the identity, and comparisons
compose transitively through any intermediate family. These identities
follow by testing on the covering colimit charts and cancelling the
intermediate coordinate equivalence. `toFrameBundleIso` compares any
family with the fixed choice used by `frameBundle`, over the original
base scheme.

This is derived internal infrastructure. It uses the genuine frames,
their duals, their restriction and composition identities, and the
previously constructed gluing comparison. It invokes no new external
source assertion. Only choices of frames on the fixed cover are compared
here. Comparison across covers, tensoring by an invertible sheaf, a
tautological invertible sheaf, and ordinary moduli representability
remain further work.
