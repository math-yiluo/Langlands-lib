# Compact quotient L² averaging and absolute unfolding

`Langlands.QuotientIntegration.quotientL2Unfolding` proves the unchanged
published proposition `QuotientL2UnfoldingStatement.{uG}`. The module also
exports `Langlands.QuotientIntegration.integrable_compact_quotient_unfolding`
for a specified strongly measurable function `ψ` satisfying `MemLp ψ 2 ν`.
Both results allow an arbitrary group universe.

## Measures and quotient conventions

Write `π(g) = Hg` for the existing left quotient by the closed subgroup `H`.
The group is locally compact, Hausdorff and second countable, with its
Borel structure; the subgroup and quotient carry their stated Borel
structures. The subgroup measure `μH` is s-finite, right invariant and
finite on compact sets. The ambient measure `μG` and quotient measure `ν`
are finite on compact sets.

The supplied hypothesis `IsCompatible H μG μH ν` concerns these actual
measures. It includes nonzeroness, regularity and right invariance of `ν`,
integrability of compact test averages, and the exact normalization

\[
  \int_{H\backslash G}\int_H t(hg)\,d\mu_H(h)\,d\nu(Hg)
  = \int_G t(g)\,d\mu_G(g)
\]

for continuous compactly supported complex tests `t`. The averaging
formula uses the supplied right invariant measure because the cosets
are `Hg`. The proof introduces no probability normalization, scalar factor
or modular correction, and assumes no finite total quotient volume.

## Compact averaging and the Hilbert functional

For `f : C_c(G, ℂ)`, let

\[
  A_f(Hg)=\int_H f(hg)\,d\mu_H(h).
\]

The proof applies the published `quotientAverageRealPositive` to the real
and imaginary parts of `f` through `complexifyCompactMap`. This constructs
a compactly supported continuous complex quotient function `C`.
The published closed-subgroup fiber-integrability theorem and
`complexifyCompactMap_eq_quotientAverage` identify `C` pointwise with
the actual `quotientAverage H μH f`. Thus continuity and compact support
are conclusions of the construction.

Continuity, compact support and finiteness of `ν` on compact sets imply
`MemLp A_f 2 ν`. The vector `v` is `MemLp.toLp A_f`, with its supplied
almost-everywhere equality to `A_f`. The continuous complex-linear form
is `innerSL ℂ v`, so `ℓ(φ) = inner ℂ v φ`. Mathlib's inner product is
conjugate linear in the first argument and linear in the second.

## Absolute convergence for a specified function

The helper keeps the given function `ψ : LeftQuotient H → ℂ` in both
actual integrals. It proves

\[
  F(g)=\overline{f(g)}\,\psi(\pi(g))\quad\text{is integrable against }\mu_G,
  \qquad
  \int_G F\,d\mu_G=\int_{H\backslash G}\overline{A_f(q)}\,\psi(q)\,d\nu(q).
\]

Strong measurability of `ψ`, together with the measurable quotient map,
makes `F` strongly measurable. Apply the positive real compact averaging
map to `g ↦ ‖f(g)‖`, obtaining a real compact quotient function `a`.
Its compact support gives `MemLp a 2 ν`, and `MemLp.integrable_mul`
applies Hölder with exponents two and two to make
`q ↦ a(q) * ‖ψ(q)‖` integrable.

The published orbital kernel is
`κ(Hg) = Measure.map (fun h : H => h.val * g) μH`.
The theorem `orbitKernel_comp` identifies its composite with `ν` exactly
as `κ ∘ₘ ν = μG`, using compact-test compatibility. For each coset the
fiber function is integrable: `ψ(π(hg)) = ψ(π(g))`, while the compact
support of `f` and closedness of `H` give integrability of `h ↦ f(hg)`.
The same constancy and multiplicativity of the norm give, at every coset,

\[
  \int_G \|F(g)\|\,d\kappa(q)(g)=a(q)\,\|\psi(q)\|.
\]

`Measure.integrable_comp_iff` therefore proves integrability against
`κ ∘ₘ ν`, and hence against `μG`. For the complex integrand this is
absolute convergence.

## Kernel Fubini and the L² representative

`Kernel.integral_comp` supplies Bochner Fubini after this integrability
has been established. On each fiber, pull out the constant `ψ(q)` and
commute complex conjugation with the integral. The inner integral becomes
`star (A_f q) * ψ q`, giving the helper's asserted equality.

For the main theorem apply the helper to Mathlib's chosen strongly
measurable representative of each `φ : Lp ℂ 2 ν`, using
`Lp.stronglyMeasurable` and `Lp.memLp`. Then `L2.inner_def` and the
almost-everywhere equality of `v` with `A_f` identify the quotient
integral with `inner ℂ v φ`. Thus the ambient formula uses that chosen
representative and has the value of the Hilbert pairing. The helper
remains available when a subsequent application needs its own specified
strongly measurable representative rather than a substituted `Lp`
representative.

## Provenance and scope

This is a derived analytic proof of the existing published statement,
using its compact averaging and orbital-kernel dependencies and pinned
Mathlib's Hölder, kernel composition, Bochner integral and Hilbert-space
APIs. The statement's Getz–Hahn §9.2 motivation and source conventions
remain as documented in its paired Markdown; no new assertion is
attributed here to that source.

Worker 116 authored the Lean proof and its initial explanation in shared
draft revision 32 of task `34b81620-20d7-4059-9b08-6bedd1c1c029`.
Worker 1684 adopted that Lean module unchanged against the current public
dependencies, expanded this explanation, and prepared the focused proof
submission.

The scope is compact quotient averaging, its L² vector and continuous
test form, absolute convergence and the stated unfolding identity. The
compact-period transform, smoothness, test separation, cuspidal
closedness, finite-volume and spectral results remain separate work.
