# Compact open orbit restriction for a compatible quotient measure

Author: Worker 88.

`Langlands.QuotientIntegration.CompactOpenOrbitMeasureStatement` is a
proposition defining an internal measure-theoretic prerequisite. This module
states it; it does not prove it or construct a compatible quotient measure.
Its provenance is the already published compact-continuous complex Weil
formula in `IsCompatible`, from
`Langlands.Analysis.Local.QuotientMeasure`, together with the actual quotient
topology and projection in `Langlands.Analysis.Local.QuotientTopology`.
It is not attributed to a separately named external theorem.

The statement quantifies a group `G : Type uG` in an arbitrary universe,
with a Hausdorff, locally compact, second-countable topological group
structure and a Borel measurable structure. It quantifies a closed subgroup
`H`, a Borel measurable structure on `H`, and a Borel measurable structure on
the existing left quotient `LeftQuotient H`. The supplied measures `μG` and
`μH` are regular Haar measures, and `μH` is also right invariant. The latter
is the orientation required by `IsCompatible`: subgroup averaging integrates
`h ↦ f(h g)` on the left cosets `H g`. No normality of `H` or right invariance
of the ambient Haar measure is an additional hypothesis.

For every compact open subgroup `K : OpenSubgroup G`, every actual measure
`μ` satisfying `IsCompatible H μG μH μ`, and every `g : G`, the statement
uses only local bindings:

- `q = leftQuotientMap H`;
- `Cg = {q (g k) | k ∈ K}`, the right `K` orbit of the coset `H g`;
- `Sg = {h : H | g⁻¹ h g ∈ K}`, the subgroup of `H` lying in `g K g⁻¹`;
- `c = μH Sg`;
- `κ = μG.restrict K`.

The precise conclusion is `0 < c`, `c < ⊤`, and the equality of measures

```text
μ.restrict Cg = c⁻¹ • Measure.map (fun k => q (g * k)) κ.
```

Here `c : ℝ≥0∞`, and both its inverse and its scalar action on measures are
the extended nonnegative real operations. This is a full equality of
measures. There is no hypothesis that `μG K = 1`: the pushforward retains
the actual mass of `κ`. Consequently the total-mass specialization is
`μ Cg = μG K / c`; this consequence is explained here but is not a separate
conjunct of the Lean declaration. When `μG K = 1`, the same formula directly
specializes to the normalization used in quotient Iwasawa integration.

The proposed proof, left to the proof successor, tests `IsCompatible` with
the pullback of a compactly supported continuous quotient test multiplied
by the indicator of `g K`. The set `g K` is compact and open, so this
product is again an admissible compact continuous test. On `Cg` its fiber
average is `c` times the quotient test; outside `Cg` it vanishes. Right
invariance of `μH` supplies independence of the representative. Left Haar
invariance of `μG` transports the ambient integral from `g K` to `K`.
Regular measure extensionality then gives the displayed restriction
formula. Positivity and finiteness of `c` follow from the nonempty compact
open subgroup `Sg` of `H`.

This proof route supplies provenance and is not an extra assumption.
Compatibility already includes quotient regularity, right invariance,
integrability of averages of compact continuous tests, and their Weil
formula. No additional orbital disintegration, orbit-mass value or
averaging identity is assumed. Separate pointwise averaging conclusions
are not asserted as consequences of measure equality alone.
