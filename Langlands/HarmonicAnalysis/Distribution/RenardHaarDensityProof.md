# Haar integration positivity and density embedding

This proof unit addresses the actual integration and density maps of Renard
II.3.6, printed pp.46–47 / PDF pp.52–53. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July
2026, registered as `renard-2026-representations-groupes-reductifs-padiques`.
The support equality is the derived bridge specified in the published
`DensityEmbeddingStatement`.

The integration functional is strictly positive because its imaginary part
vanishes on real tests and its real part is the integral of a continuous,
nonnegative, nonzero function against a measure positive on nonempty opens.
Left invariance is the actual left-translation change of variables for Haar
integration.

For a locally constant density `f`, the associated distribution annihilates
every test vanishing on the nonzero locus of `f`. This gives one support
inclusion. If a point where `f` is nonzero were outside the distribution support,
choose a compact clopen neighborhood in the complement of that support on which
`f` is constant. Its characteristic test has distribution value both zero and
`f(x)` times its strictly positive measure, a contradiction. This proves equality
of the actual distribution support with the nonzero locus of `f`.

Support equality applied to a difference proves density injectivity. For tests,
the same equality identifies the distribution support with the compact support
of the original test and proves membership in the existing submodule
`compactlySupported`. The arguments for support and positivity are formulated
for arbitrary locally compact, Hausdorff, totally disconnected spaces with
measures finite on compact sets and positive on nonempty open sets. Their Haar
specialization is the exact theorem `densityEmbedding`, retaining the group
universe and all published hypotheses.
