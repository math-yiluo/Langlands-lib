# Quotient comparison with a kernel intersection

This internal construction defines `SubgroupFunctor.kernelIntersection F q` as
the intersection of `F` with the full scheme-theoretic kernel range of `q`.
Its membership theorem holds on every test scheme, including nonreduced tests.
No representability, smoothness or normality of `F` is assumed by this
definition.

The basic comparison theorem starts with an actual `IsFppfImage E E' q`.
It assumes `E ≤ F`, that the image of `F` lies in `E'`, and that the
intersection of `F` with the full kernel lies in `E`. It proves `F = E`.
In particular the whole kernel need not lie in `E` or `F`.

The proof uses the representatives and fppf restriction supplied by
`IsFppfImage`. For a test point of `F`, it pulls back the restriction map
along the point of the represented quotient subgroup. On this actual fppf
cover the point has the same quotient image as a point of `E`. Their
difference lies both in `F` and in the full kernel, so the assumed kernel
comparison puts it in `E`. Multiplication then puts the original restricted
point in `E`. The monomorphic representative of `E` descends this membership
through the cover. No global lift on the original test scheme is used.

The commuting-square consumer applies this result to `F.comap i`. It assumes
ordinary image containments for the two horizontal comparisons, an actual
fppf image for the subgroup quotient, comparison on the quotient, and the
kernel-intersection containment. The commuting square transports membership
to the quotient; the basic theorem gives equality on all tests.

The additional kernel-representative lemma obtains the required containment
from comparison after pulling back to any homomorphism whose all-test range is
the entire kernel range. This lemma does not assume such a representative
exists.

These are internal deductions from the published full kernel, subgroup
inverse-image, `IsFppfImage`, and fpqc membership-descent interfaces. They do
not assert quotient existence or any semigroup intersection theorem without
the displayed quotient and kernel comparisons.
