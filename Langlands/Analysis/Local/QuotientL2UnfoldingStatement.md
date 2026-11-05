# Compact quotient averaging in L² and absolute unfolding

`Langlands.QuotientIntegration.QuotientL2UnfoldingStatement` is an internal
analytic step toward the compact-period argument of Getz–Hahn, §9.2. It is a
proposition definition, not a proof.

For a locally compact Hausdorff second countable topological group `G` with
its Borel measurable structure, let `H` be a closed subgroup. The subgroup
measure `μH` is s-finite, right invariant and finite on compact sets. Both
the ambient measure `μG` and the quotient measure `ν` are finite on compact
sets. The hypothesis `IsCompatible H μG μH ν` is the existing property of
actual measures: it includes the compact-test Weil integration formula,
regularity, nonzeroness and right invariance of the quotient measure. This
statement does not construct a compatible quotient measure.

For every actual compactly supported continuous complex function `f` on
`G`, its existing orbital average

\[
 A_f(Hg)=\int_H f(hg)\,d\mu_H(h)
\]

is continuous and compactly supported. There exist an actual vector
`v : Lp ℂ 2 ν` agreeing almost everywhere with `A_f`, and a continuous
complex-linear form `ℓ` on that L² space, such that every L² vector `φ`
satisfies

\[
 \int_G |\overline{f(g)}\,\phi(Hg)|\,d\mu_G(g)<\infty,\qquad
 \ell(\phi)=\langle v,\phi\rangle
   =\int_G\overline{f(g)}\,\phi(Hg)\,d\mu_G(g).
\]

The Lean conclusion states absolute convergence as `Integrable` of the
complex integrand. The pairing is conjugate linear in its first entry and
linear in its second. `φ` in the ambient integral is Mathlib's chosen
measurable representative of its L² class. The equality with the Hilbert
pairing ensures that the integral depends only on that class. There is no
point evaluation asserted as a continuous operation on L².

The quotient consists of left cosets `H * g`, so orbital averaging uses a
right invariant subgroup measure. No normality, compactness of `H`, finite
total quotient volume, unimodularity or separability hypothesis on a
coefficient Hilbert space is imposed. The group has an arbitrary universe.

## Provenance and intended proof

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§9.2, printed pp.242–246, one-based PDF pp.254–258, supplies the
compact-period/Poincaré construction and its integration argument, especially
Lemmas 9.2.4–9.2.6. The complete registered October 2026 errata is part of
the source convention; its §9.2 corrections concern the quotient and
character formulas. The statement here is a derived generic analytic step,
without the character or modular correction in the full construction.

The existing real compact averaging map, extended by real and imaginary
parts, gives `A_f` as a compactly supported continuous complex function.
Finite measure on compact sets makes it an L² vector. For absolute
convergence, average `‖f‖` along `H` and apply Hölder with exponents two and
two to this compact quotient function and `‖φ‖`. The actual orbital kernel
and the compatible Weil formula then transfer that integrability to `G`;
Bochner Fubini identifies its integral with the L² pairing. The continuous
form is the existing Hilbert inner-product form for `v`. This route is a
proof plan, not accepted proof evidence.

## Remaining obligations

An independently reviewed exact-target proof remains necessary. This
statement does not construct the compact-period Poincaré transform, its
character and modular factors, compact-period test separation, parabolic
constant terms or the all-parabolic cuspidal subspace. In particular it
does not prove GH Theorem 9.1.2, cuspidal closedness, trace class, spectral
decomposition, smoothness, reduction theory or a general finite-volume
theorem. The specialization to the actual positive split-centre adelic
quotient and the subsequent compact-period argument remain separate work.
