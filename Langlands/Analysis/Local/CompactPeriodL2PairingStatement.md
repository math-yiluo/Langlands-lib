# Compact-domain L² period pairing with the right-Haar modular factor

`Langlands.QuotientIntegration.CompactPeriodL2PairingStatement` is an
internal continuous analytic target for the pairing step in Getz–Hahn,
§9.2. It is a proposition definition, not a proof.

Let `G` be a locally compact Hausdorff second countable Borel topological
group with an actual left Haar measure `μ`. The ambient right measure is
the actual inverse measure `μ.inv`. Let `Γ` be a closed subgroup, with an
s-finite right-invariant measure `μΓ` finite on compact sets. The actual
quotient measure `ν` is finite on compact sets and satisfies the existing
`IsCompatible Γ μ.inv μΓ ν` property. Compatible-measure existence is not
asserted by this target.

Let `X` be an independently sized locally compact Hausdorff second
countable Borel space with measure `μX` finite on compact sets. Let `s`
be measurable with compact closure, and let `j : X → G` and `w : X → ℂ`
be continuous. For an actual `f : C_c(G, ℂ)`, form

\[
 k(g)=\int_s w(x)f(j(x)^{-1}g)\,d\mu_X(x).
\]

There exist an actual quotient vector `v : Lp ℂ 2 ν` agreeing almost
everywhere with `quotientAverage Γ μΓ k`, and a continuous complex-linear
form `ℓ`, such that every actual quotient L² vector `φ` satisfies

\[
 \ell(\phi)=\langle v,\phi\rangle
 =\int_s \overline{w(x)}\,\Delta(j(x))
       \left(\int_G\overline{f(g)}\,
          \phi(\Gamma j(x)g)\,d\mu^{-1}(g)\right)d\mu_X(x).
\]

The target explicitly asserts absolute integrability of the corrected
outer function and of the joint function

\[
 (g,x)\longmapsto
 \overline{w(x)}\,\overline{f(j(x)^{-1}g)}\,\phi(\Gamma g)
\]

for `μ.inv.prod (μX.restrict s)`. These convergence conclusions justify
the Fubini step. They are not supplied as assumptions. The function
representing `φ` is Mathlib's chosen measurable L² representative.
Equality with the Hilbert pairing makes the functional depend only
on the L² class. No bounded point evaluation or bounded raw period
operator on L² is assumed.

The modular character is Mathlib's actual `modularCharacter` of `G`.
For a left Haar measure, right pushforward by `a` scales it by
`Delta(a)`. Consequently left pushforward of `μ.inv` by `a⁻¹` scales
the right measure by `Delta(a)`, yielding exactly the displayed factor.
The Hilbert pairing is conjugate linear in `v` and linear in `φ`, which
explains the conjugation of the test function and weight.

## Provenance and remaining obligations

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§9.2, printed pp.244–246, one-based PDF pp.256–258, constructs the
auxiliary test in (9.11), unfolds in Lemma 9.2.5, and obtains the
modular-corrected period identity in Lemma 9.2.6. Proposition 9.2.2
uses those continuous Hilbert-space forms together with test separation.
The complete October 2026 errata inserts `χδ_G` in the indicated
intermediate formula and corrects the period quotient.

This target gives the continuous arbitrary-weight compact-domain
pairing step using actual orbital integrals, measures and L² classes.
It does not choose a fundamental domain, identify the domain integral
with an actual compact quotient period, assert smoothness or specialize
the weight to a quasi-character. A character adapter must respect the
displayed conjugation: a weight satisfying
`conj(w(x)) * Delta(j(x)) = chi(x)⁻¹` gives that period coefficient.
No quasi-character unitarity is silently assumed.

An independently reviewed exact-target proof remains required. Actual
adelic period normalization, relatively compact measurable fundamental
domains, the integrated-action comparison, period test separation,
all-parabolic cusp identification and cuspidal closedness remain further
obligations. No finite total quotient volume or spectral theorem is
asserted.
