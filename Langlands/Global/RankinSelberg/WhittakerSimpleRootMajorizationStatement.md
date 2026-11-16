# Pointwise Whittaker majorization by a global simple-root gauge

This is an internal, unproved proposition definition. It isolates the global
pointwise estimate needed by several Rankin–Selberg convergence arguments.

The source model is Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms
on GL(3) I* (1979), §2.3, printed pages 183–184, source `jps-1979-gl3-i`, and
Part II, §12.1, printed pages 226–227, source `jps-1979-gl3-ii`.
The abstract decay-space formulation is an internal generalization using the
Library's `WhittakerDecayClass`, rather than a literal transcription of a
numbered theorem in those sources.

The proposition retains an arbitrary number-field universe `u`. For every
number field `F` with `CompactSpace (AdeleQuotient F)`, rank `r+1`, complex
subspace `V` of functions on the actual carrier `Points F (r+1)` and
real-linear derivative family
`R : ArchimedeanMatrix F (r+1) →ₗ[ℝ] V →ₗ[ℂ] V`, it assumes the published
`Unfolding.WhittakerDecayClass F r V R`. Thus every vector is continuous,
left invariant under rational points, right invariant under an open finite
adelic subgroup, bounded on determinant bands, and differentiable with the
specified derivative along square-zero archimedean directions.

For a specified real exponent `β`, the extra hypothesis is

`∀ f ∈ V, ∃ B_f ≥ 0, ∀ g, ‖f(g)‖ ≤ B_f · detNorm(g)^β`.

This is a bound on the whole adelic group, stronger than boundedness on
determinant bands. The same `β` applies to every vector. In particular it
applies to every finite iterated derivative formed from `R`, since those
derivatives remain in `V`; the constants `B_f` may vary.

Under these hypotheses the statement asks for one exponent `τ ≥ 0`, chosen
before both the standard additive character `ψ` and the vector `f`. For
each such `ψ` and `f`, a gauge `Ξ` of exponent `τ` may depend on them, and
must satisfy the pointwise inequality on every actual adelic point:

`‖Unfolding.whittaker F r ψ f g‖ₑ ≤ ofReal(detNorm F (r+1) g ^ β) · Ξ(g)`.

Here `Unfolding.whittaker` is the published Whittaker integral with all
simple-root coefficients equal to one. The exponent `τ` may depend on
`F`, `r`, `V`, `R` and the specified `β`, but is uniform over `ψ` and `f`.
The hypotheses do not prescribe a central character or require cuspidality.
The phrase "central power bound" refers to the displayed determinant
weight, not an additional central equivariance hypothesis.

Keeping the determinant factor outside the gauge follows the normalization
in Part I, Proposition (2.3.6), printed p.184: for a local representation
of `GL_m` with central-character modulus `|·|^c`, that proposition bounds
the Whittaker function after twisting by `|det|^(-c/m)`. Its local
representation hypotheses and conclusion differ from this abstract global
proposition.

The source's gauge construction motivates the conclusion, but does not
supply a proof for this abstract class. A proof must derive the global
finite-place support and archimedean decay from the explicit hypotheses,
construct a Schwartz–Bruhat majorant and extend it over Iwasawa coordinates.
The cited local proposition alone does not discharge those obligations.
In particular, defining this proposition supplies no proof or assumed
axiom of global majorization. Gauge integral convergence is the separate
`AdelicSimpleRootGaugeMellinStatement`.
