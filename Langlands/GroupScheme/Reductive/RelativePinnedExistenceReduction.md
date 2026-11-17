# Reduction of coherent pinned comparisons to local existence

This internal development assembles the proved rigidity, all-test independence,
and fppf descent into the complete normalization structure. Its only supplied
mathematical hypothesis is existence of a local pinned representative in every
local-inner class. No additional literature is cited.

`HasFppfLocalPinnedRepresentatives` asserts the following, in arbitrary universe
`u`. For every two supplied affine pinned models, arbitrary common scheme `T`,
base maps `f` and `g`, and actual comparison `e`, there is a scheme `V` and a
flat, surjective, locally finitely presented map `p : V ⟶ T`, together with an
actual comparison `d` over `p ≫ f` and `p ≫ g`, such that `d` is
`IsFppfLocallyPinned` and is fppf-inner-equivalent to `pullComparison e p`.
This proposition asserts existence only. The module does not prove it.

`fppfLocalPinningPredicate` is exactly the existing `IsFppfLocallyPinned`
predicate on actual comparisons. Its locality theorem combines the existing
arbitrary-pullback law with reflection along an fppf cover.

Given `HasFppfLocalPinnedRepresentatives`,
`hasFppfLocalNormalizedComparisons_of_localPinnedRepresentatives` adds the
remaining descent conditions to each local representative. Independence on
every relative test follows from `comparisonLocalIso_isIndependent`.
Uniqueness follows from pinned inner rigidity, since two representatives
of the original comparison's inner class are inner-equivalent to one another.
`hasUniquePinnedComparisons_of_localPinnedRepresentatives` then applies the
existing fppf descent theorem: local representatives descend to unique global
representatives satisfying the same fppf-local pinning predicate.

`normalizationOfLocalPinnedRepresentatives` supplies an actual
`RelativePinnedNormalization`. It uses those unique global representatives,
the proved identity, composition and arbitrary-pullback laws of the same
pinning predicate, and its global torus and cocharacter consequences.
Finally, `relativePinnedComparisonExistence_of_localPinnedRepresentatives`
applies the existing normalization assembly to prove the unchanged
`RelativePinnedComparisonExistenceStatement`, conditional on the stated
local-existence proposition. The assembly includes the target's naturality,
composition, geometric compatibility and adjoint-section clauses through the
existing normalization construction.

There are no restrictions on the common or relative test schemes beyond
those in the unchanged target. The local-existence hypothesis is still open;
this conditional reduction is a prerequisite and is not an unconditional
proof or completion of the host task.
