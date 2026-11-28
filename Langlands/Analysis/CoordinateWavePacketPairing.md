# Pairing after Fourier integration in a common coordinate

`coordinateWavePacket` integrates the noncentral parameter in a finite
measure space and then takes the positive-phase Fourier integral in the
central coordinate `Fin m → ℝ`.

`CoordinateWavePacketPairingStatement` takes two finite noncentral
measures `α` and `β` and an s-finite common measure `μ` (a countable
sum of finite measures). The two families are jointly square integrable
for `α.prod (volume.prod μ)` and `β.prod (volume.prod μ)`, with
unscaled Lebesgue measure `volume` in the central frequency. Each
family vanishes outside a set of central frequencies of finite Lebesgue
measure. Both packets belong to L² for `volume.prod μ`, with unscaled
Lebesgue measure in the Fourier variable. Their pairing is `(2π)^m`
times the iterated integral of the `μ`-pairing at equal central
frequencies. Both pairings conjugate the second factor. The function of
the three frequencies obtained by integrating over `μ` is integrable
for `volume.prod (α.prod β)`.

The proof integrates the finite factors using `memLp_two_integral_fst`.
Fubini gives L² central slices almost everywhere, and finite support
converts them to L¹ slices. This permits `coordinatePartialPlancherel`.
To prove joint integrability of the frequency pairing, the proof pulls both
families to the four-factor product by reordering the factors and adding
one finite measure factor to each family, then applies Hölder and Fubini.
The equality follows by applying `squareIntegrableFibrePairing` at almost
every central frequency after partial Plancherel.

This is the product-measure step in the first paragraph of E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series* (2011), §8, printed p. 328 (volume PDF p. 337). The displayed
constant uses Lebesgue measure in the two central coordinates. Spectral
measure normalizations are applied when using this identity for adelic
wave packets.
