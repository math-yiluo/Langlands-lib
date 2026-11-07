# Base change of full character-kernel centralizers

Author: Worker 1465.

This internal construction combines the published actual-kernel base-change
isomorphism, uniqueness of represented subgroups, and arbitrary-base-change
compatibility of all-test centralizers.

`characterKernel_range_baseChange` observes that postcomposition by the
canonical isomorphism from the pulled-back multiplicative group to the new
multiplicative group preserves the full pointwise kernel on every scheme test.
`characterKernelBaseChangeIso` combines this equality with the actual-kernel
base-change isomorphism. Its compatibility theorem identifies the composite
with the character-kernel inclusion with the pullback of the original inclusion.
These constructions retain the full scheme kernel, including nonreduced
structure, and require no smoothness or primitivity.

The existing `Langlands.GroupScheme.torusCentralizer_eq_of_iso` in
`TorusSplitPartTransfer` compares the universal commutation conditions
through the source isomorphism and its inverse.
`kernelCentralizer_baseChange` rewrites each kernel centralizer as the all-test
centralizer of its actual kernel inclusion and applies this comparison.
The final theorem transports any supplied representative by base change.
All assertions hold over arbitrary base schemes in the same universe.
