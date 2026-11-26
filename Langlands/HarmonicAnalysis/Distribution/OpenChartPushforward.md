# Test pushforward in open charts

A measure-characterized pushforward of Schwartz–Bruhat tests along a continuous map has support in the compact image of the support of each input. In a Hausdorff, locally compact, totally disconnected target with a Borel measure finite on compact sets and positive on nonempty open sets, the proof tests any point outside the image against a compact clopen indicator. The output test is constant near that point. On a small enough indicator its integral is zero by the pushforward identity, so the constant is zero.

When a map lands in an open chart, the output test restricts to the chart because its support lies in the image. `IsTestPushforward.exists_openTarget` extends target tests by zero, applies the original integral identity, and pulls the underlying measure back by the chart embedding. `IsTestPushforward.exists_weighted` inserts a locally constant nonnegative weight on the source and a nowhere-zero locally constant nonnegative weight on the target. The proof multiplies the source test by its weight and divides the output test by the target weight.

These are changes of coordinates and measures in the test integration formula used by the submersion principle. Harish-Chandra, *A submersion principle and its applications*, §3, p. 97.
