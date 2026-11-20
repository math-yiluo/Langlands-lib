# Convolution with the actual proper source sum

In the proof of VIII.2.3, Waldspurger reduces both convolution identities to
vanishing on every packet at a proper semistandard parabolic. The exact
single-packet premise is `GlobalSynthesis.ProperPacketConvolutionVanishingStatement`.
It uses the intrinsic `rationalCuspidalSubmodule` and both orders of convolution
with `GlobalSynthesis.componentPacket`, on the full actual semistandard index.

`GlobalSynthesis.ProperSynthesisConvolutionStatement` gives both Schwartz
convolution identities with `f₂` replaced by `f₂ - κ(v)`, where `v` is a smooth
finite-support section supported on proper indices and `κ` is the conditional
`GlobalSynthesis.schwartzSynthesis`. The source group is connected reductive
over a nonarchimedean local field with finite residue field. The field and
representation carriers have independent universes. All convolutions use the
same ambient Haar measure, with `ConvolutionWeights` supplying integrability
and closure on the actual Schwartz space.

The proof takes each component Schwartz lift from the existing VI.3.1
`ComponentContinuityStatement`. It identifies the finite sum of these lifts
with `κ(v)` by the injective underlying-function map and
`GlobalSynthesis.weightedSynthesis_eq_sum`. Each summand keeps its actual source
coefficient. The two linear maps obtained by fixing the cuspidal argument
in `Space.convolutionBilin` carry the weighted sums to zero. Linearity
then gives both identities after subtraction. This is a finite sum, so passing
convolution through it uses the existing linearity with its integrability
proof and requires no interchange of two integrals.

This reduction uses VI.3.1 membership and the two single-packet vanishings as
premises. The comparison producing those vanishings uses VII.2 and VII.1.2.
For VIII.2.3 the section `v` is the proper Fourier cutoff with its finite-support
lift. The finite-sum calculation applies before specializing to that lift.

Source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of Jussieu
2 (2003), printed p. 322, proof of VIII.2.3, first reduction.
[DOI](https://doi.org/10.1017/S1474748003000082)
