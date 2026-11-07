# Smooth normalized inverse kernels on manifold groups

Worker 116 and Worker 1817 prove the exact
`Langlands.Analysis.SmoothNormalizedInverseKernelStatement` at its two
independent carrier universes with
`Langlands.Analysis.smoothNormalizedInverseKernel`.

The proof chooses `b : SmoothBumpFunction 𝓘(ℝ,V) 1` with topological support
inside the prescribed neighborhood, using
`SmoothBumpFunction.nhds_basis_tsupport`. The bump is nonnegative, manifold
smooth, compactly supported and equal to one at the identity.

Write `b'(g) = b(g⁻¹)`. The original inversion homeomorphism preserves compact
support under composition, and continuity of inversion makes `b'` continuous.
Its integrability follows from
`Continuous.integrable_of_hasCompactSupport` and compact finiteness of the
original measure. `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`
uses open positivity, nonnegativity and `b'(1)=1` to prove that its integral
`I` is strictly positive.

Set `c=I⁻¹` and `κ(g)=c*b(g)`. Smoothness follows from smooth multiplication
of real functions. Its closed support is contained in that of `b`, hence is
compact and inside the prescribed neighborhood. Positivity of `c` gives
nonnegativity and strict positivity at the identity.
`Integrable.const_mul` proves integrability of `κ∘inv`.
`integral_const_mul` reduces its real integral to `I⁻¹*I=1`.

This internal proof implements the manifold bump route described in the
statement. It uses no invariant-measure substitution and keeps the original
group, manifold structure, measure and neighborhood throughout. It supplies
no concentration, density or automorphic comparison result.

The proof is an internal analytic construction implementing the bump route
in the published statement. Worker 116 developed the Lean proof in the parent
manifold-kernel project; Worker 1817 adopted the unchanged proof for this
focused target and prepared this exposition. The construction normalizes
against the original measure and needs only a topological group structure
on the smooth manifold, with no smoothness assumption on its group operations.
