# Retained Laurent clearing of gamma equations

This internal algebraic and analytic bridge retains an actual finite clearing
kernel when passing between gamma functional equations and bilateral coefficient
identities. It is intended for the second-block continuation in the adjacent
rank argument.

Suppose `K • a` is the finite Laurent polynomial `L`, and the finite kernels
`A` and `B` satisfy `map A = map B * G` in rational functions. Given separately
convergent original and dual spectral expansions, the scalar gamma equation
implies

`(B * K) • reflectSeries q ad = (C (ζ^e) * A * K) • a`.

The proof first identifies `map L = map K * R`. The rational formulation of the
gamma equation then shows that the reflected finite polynomial
`reflectLaurent q (C (ζ^e) * A * L)` clears the dual rational value by
`reflectLaurent q (B * K)`. Spectral coefficient uniqueness on the dual
expansion's own right half-plane identifies its coefficients. Reflecting this
finite identity gives the displayed equation. The original and dual convergence
half-planes need not intersect.

Conversely, the displayed coefficient identity and finite original clearing
give a finite cleared dual series after reflection. Convergent spectral sums
identify both cleared rational values. When `B` and `K` are nonzero, cancellation
in the rational-function field recovers the original gamma equation on its full
published domain.

The helper lemmas extend spectral clearing from polynomial kernels to arbitrary
finite Laurent kernels, and verify compatibility and involutivity of finite and
bilateral reflection. No Laurent kernel is cancelled on the unrestricted
bilateral series module. The result does not assert a gamma factor for a
representation or supply a real-parameter identity.

Provenance is internal composition of published spectral uniqueness, Laurent
evaluation, rational gamma comparison, and finite reflection. This is not a
separate assertion attributed to the literature.
