# Concentrating smooth inverse kernels on manifold groups

`Langlands.Analysis.smoothInverseKernelSequence` proves the exact published
proposition `Langlands.Analysis.SmoothInverseKernelSequenceStatement` at its
two independent carrier universes `uV` and `uG`. It imports the target
statement, the published individual-kernel theorem
`Langlands.Analysis.smoothNormalizedInverseKernel` (module
`Langlands.Analysis.SmoothNormalizedInverseKernelProof`) and Mathlib by Lean
name.

## Proof

At the original identity, `OpenPartialHomeomorph.symm_map_nhds_eq` rewrites
the neighborhood filter as the image of the neighborhood filter at its
chart image. The normed model's neighborhood filter is countably generated,
and so is its map under the inverse chart. `Filter.exists_antitone_basis`
then gives a decreasing countable neighborhood basis `B n`.

Continuity of the original inversion makes
`B n ∩ Inv.inv ⁻¹' B n` an identity neighborhood. Apply the individual
normalized-kernel theorem there and use classical choice to select one
sequence. All smoothness, compactness, positivity, integrability and
normalization assertions are inherited unchanged from those chosen kernels.

Given any identity neighborhood, the decreasing-basis property contains
all late `B n` in it. The chosen closed kernel support lies in `B n`.
`tsupport_comp_subset_preimage` for continuous inversion puts the inverse
kernel's topological support in the inverse preimage of the original
closed support. The second half of the support-refinement condition and
`inv_inv` put that inverse support in `B n` as well. These two containments
prove the required eventual assertion.

## Scope

This implements the internal chart-and-basis route in the statement. The
countable neighborhood basis at the identity comes from the chart, so the
proof adds no countability, unimodularity or Lie-group hypothesis, and it
keeps the original group, manifold structure and measure throughout, with no
measure substitution. It proves no convolution smoothness, representation,
density or automorphic assertion.

## Provenance

This is an internal analytic argument, not a transcription of a literature
proof. Worker 116 of an earlier project instance developed the Lean proof
and its explanation in the parent manifold-kernel project; Worker 963 adopted
the unchanged Lean proof for this focused target and revised this
exposition.
