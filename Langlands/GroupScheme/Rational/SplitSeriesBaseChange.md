# Scalar extension of represented split series

This internal construction extends an actual finite represented normal series
with additive-group quotients along an arbitrary field extension. The two
fields have the same arbitrary universe `u`. There is no separability,
algebraicity, finiteness or characteristic restriction on the extension.

`IsVectorGroupOfDimension.baseChange` transports the given natural all-test
vector coordinates through the actual pullback point equivalence. Existing
naturality of those transported coordinates proves the vector-group predicate
with exactly the original dimension.

`HasSplitSeries.baseChange` assumes the original group is affine and preserves
the length of its supplied series. The proof is induction on that length. In
length zero, the identity range commutes with base change, as does the bottom
subgroup functor. In a successor step it pulls back the original closed
inclusion and fppf quotient. Closedness, smoothness, normality, the fppf cover
properties and its exact all-test kernel are preserved by existing base-change
lemmas. The original kernel is affine because it is closed in the affine
ambient group. Together with its supplied smoothness and connectedness this
makes it geometrically connected, so its pullback remains connected. The
vector quotient has the same one-dimensional natural coordinates after
extension. Induction supplies the shorter series on the actual pulled-back
kernel. Thus no surjectivity on each original test's point group is asserted.

`IsSplitUnipotent.baseChange` forgets the chosen length after applying that
same-length result. `baseChangeSplitSeries` retains a supplied length and its
proof while changing the field; its length equality is definitional. Neither
ambient smoothness nor ambient connectedness is an extra premise: the
induction only uses those properties on kernels where the series supplies
them. Affineness remains an explicit premise.

The provenance is internal composition of natural vector-coordinate base
change, represented fppf-kernel base change, all-test subgroup base change,
and geometric connectedness of smooth connected affine groups over fields.
This construction does not assert that splitness descends from an arbitrary
field extension or prove rational maximal-torus conjugacy.
