# Compact test function from a weighted compact-domain period

`Langlands.QuotientIntegration.CompactPeriodTestStatement` is an internal
construction target for the test function used in the compact-period
argument of Getz–Hahn, §9.2, equation (9.11). It is a proposition
definition, not a proof.

Let `G` be a first countable Hausdorff topological group, and let `X` be a
topological space with its Borel measurable structure. The actual measure
`μ` on `X` is finite on compact sets. Let `s` be a measurable subset with
compact closure, `j : X → G` a continuous map, `w : X → ℂ` a continuous
weight, and `f : C_c(G, ℂ)` an actual compactly supported continuous test
function.

For every `g : G`, the following integral is absolutely convergent, and
there exists an actual compactly supported continuous function `k` with

\[
 k(g)=\int_s w(x)\,f(j(x)^{-1}g)\,d\mu(x),\qquad
 \operatorname{supp}_{\rm top}(k)
 \subseteq j(\overline{s})\operatorname{supp}_{\rm top}(f).
\]

The Lean support is topological support, the closure of the nonzero set.
The existence of `k : C_c(G, ℂ)` includes continuity and compact support;
these are conclusions rather than input fields. No measure normalization,
finite total measure on `X`, subgroup embedding, compactness of `X`,
group structure on `X` or countability premise on `X` is imposed. First
countability of `G` is retained for the dominated-continuity theorem used
in the intended proof; the actual adelic groups satisfy this hypothesis.
The group and
parameter space have independent universes.

## Source and scope

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§9.2, Lemma 9.2.4, printed p.244, one-based PDF p.256, equation (9.11),
uses a relatively compact measurable fundamental domain for a compact
period quotient to form the auxiliary test function. Here `X` may be
that period group, `j` its inclusion in the ambient group, and `w=χ⁻¹`.
The complete October 2026 errata corrects the compact-period quotient
after (9.9) and the character/modular formula in Lemma 9.2.6.

The target is a derived continuous version of the compact-domain
construction. It neither selects a fundamental domain nor proves its
existence. It does not assert that the supplied weight descends to a
quotient. The source's smoothness conclusion, equality with the full
periodized Poincaré series, its character and modular correction, period
test separation and cuspidal closedness remain further obligations.
An independently reviewed exact-target proof is required.
