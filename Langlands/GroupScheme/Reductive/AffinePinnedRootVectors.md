# Actual pinning points over arbitrary test schemes

This internal module extends each original affine pinning vector to any test
ring and regards its actual dual-number point as a point of the pulled-back
model over an arbitrary common scheme. A compatible affine test map supplies
the base map; the point is defined by the actual scheme pullback universal
property.

The two projection identities describe the point explicitly. The pullback law
compares direct and iterated pullbacks through `baseChangeCompIso` and its
projection. It follows by the pullback universal property and the published
projection identity for that isomorphism.

The test ring is an arbitrary commutative ring, and the common schemes are
arbitrary. This constructs actual pinning points and their transport. It does
not assert that the full weight space over the test ring is their span, or
prove local pinned normalization or its uniqueness.
