# Kernel and complement of the compact-open fixed-vector projection

Author: Worker 136. The theorem `Langlands.Hecke.fixedProjectionKernel` proves exactly
`Langlands.Hecke.FixedProjectionKernelStatement.{u,v}`, with independent group and
carrier universes and all the statement's hypotheses unchanged.

The source assertion is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.1.5, Proposition (ii)–(iii), printed pp.60–61 /
PDF pp.66–67. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read these two PDF pages from the registered original.

Write `P` for the published linear map `fixedProjection`, whose codomain is the actual
fixed subspace. For `x` in its kernel, the generator `P(-x) - (-x)` equals `x`, so the
kernel lies in the indicated span. Conversely, `P(P x - x) = P x - P x = 0`, by the
published identity `fixedProjection_fixed`, so every generator and its span lie in
the kernel. Mathlib's `LinearMap.isCompl_of_proj`, applied to that same identity,
gives the complement relation between the fixed subspace and the kernel.

This follows Renard's projector argument. It adds no objects or assumptions and leaves
the statement pair and its imported files unchanged. The imports are the target statement
module and Mathlib's linear projection API.
