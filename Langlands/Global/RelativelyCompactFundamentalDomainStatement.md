# Relatively compact Borel fundamental domains

`Langlands.Global.LeftCosetSpace.RelativelyCompactFundamentalDomainStatement`
applies to a discrete subgroup `Γ` of a locally compact, Hausdorff,
second-countable topological group `H` with its Borel measurable structure.
The additional input is an actual compact set `K` meeting every left subgroup
orbit: for every `x`, some `γ : Γ` has `γ * x ∈ K`.

The conclusion supplies one measurable set `s` with compact closure and,
for every `x`, exactly one `γ : Γ` carrying `x` into `s`. Thus `s` is a
Mathlib fundamental domain for every ambient measure, independently of
invariance. For every `Γ`-invariant measure `ν`, the actual quotient
projection from `ν.restrict s` preserves the existing
`discreteQuotientMeasure Γ hΓ ν`; this identifies the new domain with the
already defined quotient measure.

For every measure finite on compact sets, `ν s < ∞`. If that measure is
also nonzero and `Γ`-invariant, `normalizedMeasure Γ ν s` is a probability
measure and equals normalization using the original
`fundamentalDomain Γ hΓ`. The positive mass needed for normalization is a
consequence of countable invariant translates covering the group. It is
not an additional hypothesis.

This is an internal refinement of the published first-patch construction in
`Langlands.Global.LeftCosetFundamentalDomain`, using the pinned Mathlib
local-compactness, covering, Lindelöf and fundamental-domain APIs. Thicken
`K` to an open set `V` with compact closure; intersect the countable
injective quotient patches with `V`; then take the first patch in each
quotient fiber. The resulting Borel transversal lies in `V`. The
statement does not assert `s ⊆ K`.

The application motivating this refinement is the compact-period argument
in Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§9.2, printed pp. 242–246, especially (9.9), (9.11), and
Lemmas 9.2.4–9.2.6. The October 2026 errata corrects the compact quotient
immediately after (9.9). This target supplies the analytic selection and
measure comparison step; the existence of `K` for each actual unipotent
rational quotient, the character and integrated-action comparison, test
separation, and the all-parabolic cuspidal closedness theorem remain
separate obligations.
