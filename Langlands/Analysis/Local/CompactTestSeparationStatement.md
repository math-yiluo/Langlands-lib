# Compact continuous tests separate locally integrable functions

`Langlands.Analysis.CompactTestSeparationStatement` applies to any
locally compact, Hausdorff, second-countable space `X` with its Borel
measurable structure, any measure `μ` on it, and any specified locally
integrable complex function `F`.

It asserts both:

- For every actual `f : C_c(X, ℂ)`, the function
  `star(f(x)) * F(x)` is absolutely integrable.
- `F` vanishes almost everywhere if and only if its integral against
  every such conjugated test is zero.

The measure need not be finite, finite on compact sets, Haar, regular,
or nonzero. Local integrability supplies the integrability on compact
sets used in the argument. There is no group structure or smoothness
assumption on `X`.

This is an internal analytic prerequisite for the period-test
characterization in Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §9.2, Lemma 9.2.3, printed p. 243
(one-based PDF p. 255), and the kernel characterization in the proof of
Proposition 9.2.2, printed p. 246 (PDF p. 258). The source uses smooth
compact tests in its automorphic setting. The present target concerns
all compact continuous tests in the stated topological generality.

The internal route uses compact Urysohn cutoffs: for a compact set `K`,
choose `ρ` valued in `[0,1]`, with compact support and `ρ = 1` exactly
on `K`. Then `ρ^(n+1)` converges pointwise to the indicator of `K`,
and local integrability gives an integrable compactly supported
majorant. Dominated convergence recovers zero integrals on all compact
sets, which determine almost-everywhere vanishing.

The application must still prove local integrability and the tested
integral identities for the actual normalized L² period. The actual
quotient-period/continuous-linear-form comparison and all-parabolic
cuspidal identification remain separate obligations. The comparison
with the source's literal smooth test space is also retained.
