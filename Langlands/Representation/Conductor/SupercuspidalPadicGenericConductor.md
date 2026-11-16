# Generic and newvector conductors for supercuspidal p-adic representations

Worker 619, Task 7045. This is a derived comparison lemma at independent field
and representation universes `uF uV`. It uses
`SupercuspidalPadicConductorExponentStatement` as a premise and proves none of
that premise's existence assertions without it.

The first import, `SupercuspidalPadicConductorExponentStatement`, supplies the
restricted JPSS conductor proposition and the canonical p-adic structures.
The second, `GenericEpsilonConductor`, supplies the constructed generic
conductor and its identification with any certified epsilon exponent when the
additive character has conductor `𝔒`.

The proof chooses a uniformizer with the normalized absolute value using
`HighlyRamified.exists_uniformizingElement_normalizedAbs` and supplies
`HighlyRamified.normalizedAbsoluteValue_eq_one`. It applies the restricted
premise to the given supercuspidal representation, the Borel structures and
the actual self-dual Haar measure `Correspondence.localSelfDualHaar`, certified
by `Correspondence.isSelfDual_localSelfDualHaar`. The equality
`genericConductor_eq_of_hasIntegerConductor` identifies the resulting exponent
with the constructed conductor. The newvector and one-dimensional fixed-space
assertions come directly from the premise.

The local nonarchimedean additive-group instance follows from
`IsLinearTopology.hasBasis_open_submodule` for the valuation ring. The norm,
valuation and local-field instances are the canonical ones, as in
`GenericEpsilonConductor`. No field structure or published module is changed.

This proof adapts the comparison in `GenericEpsilonConductor` and the bridge
sketched in the published target's Markdown. Its mathematical input is exactly
the restricted JPSS 1981 Theorem (5.1) already documented there. It invokes no
full generic conductor theorem and introduces no new literature assertion.
