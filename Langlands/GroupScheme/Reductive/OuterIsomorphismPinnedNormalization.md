# Pinned comparison normalization on actual isomorphism schemes

This internal derived construction transfers supplied relative pinned
normalization to actual isomorphisms between iterated pullbacks of two supplied
affine pinned models. The models may have different affine bases, coordinate
ranks and root data. Every scheme test and every refinement is retained.

The canonical direct and iterated pullback identifications give an equivalence
between direct comparisons and isomorphisms of the iterated pullbacks.
The three-step pullback comparison identity proves that this equivalence
commutes with arbitrary refinement, including the explicitly equal endpoint
maps. Conjugation by the same actual identifications preserves fppf-local inner
equivalence.

For a supplied `RelativePinnedNormalization`, `correction_pullAlong` extends
its correction law to explicitly equal endpoint maps. It substitutes those
maps and applies the already proved direct-pullback correction law.

`RelativePinnedNormalization.actualNormalization` applies correction to the
direct comparison corresponding to each actual iterated-pullback isomorphism,
then transfers it back. The equivalence's refinement laws and the correction
law prove naturality on every relative scheme test. Correction depends only
on the fppf-local inner class, so conjugation compatibility proves invariance.
The correction's class-preservation property gives the required inner
equivalence of the original and normalized actual isomorphisms.

This is an internal derived adapter of the existing relative pinned
normalization interface and the direct/iterated base-change identifications.
It supplies the input to `ActualNormalization.pointNormalization` for any
supplied isomorphism representer and full-centre adjoint quotient of the
source. Existence of `RelativePinnedNormalization` remains an explicit input.
No geometric properties of the equalizer parameter, local pinning existence,
or final DVR outer-quotient theorem are proved here.
