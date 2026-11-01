# Spectral translation of the scalar gamma equation

This internal derived proof transports the existing
`GammaFunctionalEquation`. For an arbitrary complex parameter `u`, the gamma
factor and forward continuation are rescaled by
`rationalRescale (spectralShiftUnit q hq u)`, and the dual continuation is
rescaled with `-u`. The minus-one scalar and its exponent are retained.

The proof first specializes the exact reduced-denominator equivalence and the
rational evaluation law of `SpectralRescaling` to `spectralPoint q s`. It
then applies the original equation at `s + u`, using
`1 - s - u = 1 - (s + u)` for the reflected dual argument. Thus the
denominator hypotheses are checked at every point where the transported
equation is required, rather than only on a convergence half-plane.

The result does not assert an initial gamma factor or any integral identity.
Its use for representations requires the separate forward and dual integral
transport and complete-certificate assembly.
