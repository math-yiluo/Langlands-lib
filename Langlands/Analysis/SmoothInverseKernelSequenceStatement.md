# Concentrating smooth kernels with normalized inverse integral

Worker 116 states `Langlands.Analysis.SmoothInverseKernelSequenceStatement`
with independent universes for the real normed model `V` and group `G`.
The group is a Hausdorff topological group with its original smooth real
manifold structure modelled on finite-dimensional `V`, its Borel measurable
space, and a measure finite on compact sets and positive on nonempty open
sets. Smoothness of the group operations is not assumed.

There exists one sequence of real kernels `κ n : G → ℝ`. Each is smooth
for the given manifold structure, compactly supported, nonnegative everywhere
and positive at the identity. For the original measure, the inverse kernel
`g ↦ κ n (g⁻¹)` is integrable with real integral one. For every identity
neighborhood `U`, the closed topological supports of both `κ n` and its
inverse kernel are eventually contained in `U`. The index may depend on `U`;
the supports themselves need not be nested. The sequence is chosen before
any representation or vector.

This is an internal consequence of the individual-neighborhood proposition
`Langlands.Analysis.SmoothNormalizedInverseKernelStatement`, rather than
a separate existence convention. The intended proof derives countable
generation of the identity-neighborhood filter from one original chart:
the inverse chart maps the neighborhood filter at the image point in `V`
exactly onto the original neighborhood filter. The normed model has
countably generated point-neighborhood filters. No second-countability or
separability assumption on the whole group is needed.

Choose a decreasing countable neighborhood basis `B n` and apply the
individual-neighborhood construction inside
`B n ∩ {g | g⁻¹ ∈ B n}`. Continuity of inversion makes this intersection an
identity neighborhood. Classical choice supplies the kernels. Each kernel's
closed support lies in `B n`; the topological support under composition
with the inversion homeomorphism lies in its inverse preimage, which is
also contained in `B n`. The decreasing-basis property proves both eventual
containments for every identity neighborhood.

The normalized inverse kernels consequently have ordinary supports shrinking
to the identity, the convention required by the existing
`Langlands.Analysis.IntegratedIsometricApproximationStatement`. That
application is a separate obligation. This file defines only the proposition
and proves none of the assertions. It assumes no invariant measure,
unimodularity, inversion symmetry, chosen Haar normalization, global
countability or positive model dimension. It supplies no smooth-vector
density, compactness, self-adjointness or automorphic tensor realization.
