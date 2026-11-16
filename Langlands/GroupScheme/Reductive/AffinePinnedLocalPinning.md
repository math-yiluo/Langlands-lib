# Pinning preservation on arbitrary local affine tests

This internal module defines a concrete predicate on actual comparisons of
supplied affine pinned models. `PreservesLocalPinning` tests every map from the
spectrum of a local commutative ring into the arbitrary common scheme, with
compatible coefficient maps from both original model rings. On each such test,
some bijection of the simple-root supports carries the actual dual-number
pinning points to one another under the comparison.

The bijection may depend on the local test. Thus the definition does not select
a single constant root relabelling on a disconnected common scheme. It imposes
neither a fixed full root-datum equivalence nor a separate compatibility
condition between bijections on different tests.

Identity comparisons satisfy the predicate. Composition composes the two
bijections on each test; the intermediate coefficient algebra is recovered
from the affine test's map to the intermediate original base. Arbitrary
pullback preserves the predicate by the actual `rootVectorPoint_pull` identity
and the pullback square of the comparison.

`IsLocallyPinned` conjoins this predicate with the exact torus and cocharacter
clauses. It is closed under identity, composition and arbitrary pullback.
The construction is derived directly from the supplied pinning vectors and
scheme pullback universal properties. Geometric local existence, uniqueness
within an inner-equivalence class, and fppf reflection of this pinning predicate
are not asserted or proved here.
