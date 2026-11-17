# Global assembly from affine based pinning corrections

`FppfPinnedCorrection.ofAffineBasedInput h e` constructs a single actual fppf
pinned correction for every comparison `e` over every common scheme, assuming
`HasAffineBasedPinnedCorrections`. This input asserts that for any coefficient
ring with the two original algebra structures, every `BasedCoordinateIso`
between the corresponding model pullbacks has an actual fppf pinned
correction of its group isomorphism.

The input is a hypothesis, not a theorem proved in this module. It retains
all original pinning-vector obligations: the constructed correction must
satisfy `IsLocallyPinned`, including the exact differential equations on every
local affine test. No connectedness, affineness, quasi-compactness or
nonemptiness condition on the common scheme or the fppf correction space
appears in the resulting construction.

This is an internal deduction from `AffinePinnedBasedCorrection` and
`AffinePinnedCorrectionAssembly`:

1. `FppfPinnedCorrection.cover` presents an actual single correction cover as
   a singleton covering family. `bindCover` composes a given fppf covering
   family with a correction cover on each member. The normalized pullback
   coherence lemma converts the resulting local corrections to the direct
   composite maps, and `ofCover` collapses the family to one actual cover.
2. `absorbTargetCorrection` handles an original comparison already followed
   by an inner correction by `c`. On the later correction cover, pull `c`
   back with `pullBasePoint` and multiply the later section on its right
   by that pullback. The formula for inner conjugation by a product gives
   precisely the composite of the original correction and the later one.
   `pullComparison_trans`, `pullComparison_inner` and associativity identify
   the concretely pinned corrected comparison.
3. `exists_pinnedCorrection_at_affineMap` equips any affine test ring with
   the two algebras induced by its actual maps to the coefficient spectra.
   `Spec.map_preimage` identifies the corresponding algebra base maps with
   those supplied maps. Transport along these endpoint equalities permits
   application of the assumed affine input to the supplied based data.
4. `ofAffineBasedInput` uses the existing affine etale based-correction
   cover for an arbitrary comparison. On each chart, step 3 supplies a
   correction of the chart's based group isomorphism. Its recorded equality
   identifies that isomorphism with the original chart comparison followed
   by the initial actual target inner correction. Step 2 absorbs the initial
   correction, and step 1 composes the covers and assembles all chart
   corrections.

`fppfLocalPinnedNormalization_of_affineBasedPinnedCorrections` then proves
the exact `FppfLocalPinnedNormalizationExistenceStatement` from the stated
affine input, using the earlier source-conjugator equation. The module
provides a conditional global assembly; it does not discharge the affine
pinning-correction input or prove the parent comparison-existence statement
unconditionally.
