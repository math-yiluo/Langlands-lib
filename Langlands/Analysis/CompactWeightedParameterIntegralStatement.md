# Smooth compact scalar kernels with Banach-valued weights

`CompactWeightedParameterIntegralStatement` is an internal analytic proposition.
It states that for a compact Borel space `X` with a finite measure `μ`, a
continuous weight `w : C(X, E)` into a complete complex normed space, and a
continuous map `j : C(X, H)`, the actual vector-valued integral

`p ↦ ∫ x, h (p, j x) • w x ∂μ`

is real `C∞` on the open parameter set `s`, provided that the scalar kernel
`h : V × H → ℂ` is real `C∞` on `s × t`, `t` is open, and `j` takes values
in `t`. For every parameter in `s` the weighted integrand is also required
to be Bochner integrable.

The spaces `V` and `H` are arbitrary real normed spaces. The target `E` is
complete, but need not be finite-dimensional, Hilbert, or separable.
The four carrier universes are independent. No manifold structure on `X`,
differentiability of `j` or `w`, invariant measure, or nonzero measure is
assumed. Empty compact spaces and empty parameter domains are allowed.
No condition on the scalar kernel outside `s × t` is imposed.

The intended internal derivation uses the published compact-family theorem
`contDiffOn_infty_compactFamily_of_joint` to regard the scalar kernel as a
smooth map to `C(X, ℂ)` with its supremum norm. Integration against the fixed
continuous vector-valued weight is a bounded complex linear map, with bound
`∫ x, ‖w x‖ ∂μ`. Composing its underlying real continuous linear map with
the scalar compact-family map yields the claimed Banach-valued smoothness.
The integrability assertion follows from continuity on the compact space
at each allowed parameter.

This file defines a proposition and supplies no proof. Its analytic
application to local charts of convolution kernels on actual archimedean
groups, the change-of-variables identities for representation orbits, smooth
approximation, and automorphic tensor realization remain separate
obligations.
