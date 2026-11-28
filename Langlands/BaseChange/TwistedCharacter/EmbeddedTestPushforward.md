# Test pushforward along embedded source and target charts

Let \(P\) be a test pushforward on \(p:X\to Y\). Let \(i:X'\to X\) be an
open embedding and \(j:Y\to Y'\) an open embedding with closed image.
Suppose \(X,Y'\) are Hausdorff and the spaces have Borel measurable structures.
If the measures for \(P\) are \(\mu\) on \(X\) and the pullback of \(\nu\)
from \(Y'\) to \(Y\), then `embeddedTestPushforward` gives a test pushforward
for \(jpi\) with the pullback of \(\mu\) on \(X'\) and \(\nu\) on \(Y'\).
It extends by zero along \(i\), applies \(P\), then extends by zero along \(j\).

An integral of an extended test is an integral over the image, and hence
is the integral in the embedded coordinates against the pulled-back measure.
Closedness of the target image makes restriction of an ambient test a
test on \(Y\). Applying these identities on the two sides of the pushforward
formula proves the claim. Extension along a product of open embeddings
also preserves tensor tests by pointwise evaluation.

This permits restriction of the semisimple conjugation pushforward to a compact
source product and extension of its target to the ambient component group.
See Harish-Chandra, *A submersion principle and its applications*, §3, p. 97,
and Clozel, *Characters of nonconnected, reductive p-adic groups*, §3.4, p. 154.
