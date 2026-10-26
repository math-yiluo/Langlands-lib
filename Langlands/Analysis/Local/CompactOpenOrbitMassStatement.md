# Compact open quotient orbit averaging and mass

Author: Worker 457.

Worker 88 supplied the shared regular-Haar hypothesis interface used here.

`Langlands.QuotientIntegration.CompactOpenOrbitMassStatement` defines a
proposition about the existing actual left quotient and supplied measures.
This module states the proposition; it supplies no proof or quotient-measure
construction. Its provenance is an internal derivation from
`IsCompatible.averaging_integrable` and `IsCompatible.integral_formula` in
`Langlands.Analysis.Local.QuotientMeasure`, together with the quotient
projection and topology in `Langlands.Analysis.Local.QuotientTopology`.
It is not a transcription of a separate theorem in the JPSS literature.

The proposition quantifies every group `G : Type uG`, in an arbitrary universe,
with a Hausdorff, locally compact, second-countable topological group structure
and a Borel measurable structure. It quantifies every closed subgroup `H`,
with its subtype topology and supplied Borel measurable structure, and a
supplied Borel measurable structure on the existing `LeftQuotient H`.
The supplied `μG` and `μH` are regular Haar measures; `μH` is additionally
right invariant. These are the same explicit regular Haar hypotheses as in
the separate compact-open orbit restriction statement. There is no ambient
right-invariance premise.

For every `K : OpenSubgroup G` whose underlying set is compact, and every
supplied measure `ν` satisfying `IsCompatible H μG μH ν`, define locally

- `q = leftQuotientMap H`, the actual projection to the left cosets `H g`;
- `Ω = q '' (K : Set G)`, the orbit of the identity coset under `K`;
- `A = {h : H | h.val ∈ K}`, the subgroup intersection viewed inside `H`;
- `a = (μH A).toReal : ℝ`.

The Lean proposition states that `Ω` and `A` are each compact and open,
and that both `μH A` and `ν Ω` are strictly positive and strictly less than
`⊤`. Its pointwise conclusion, for every `x : LeftQuotient H`, is

```text
quotientAverage H μH ((K : Set G).indicator (fun _ => (1 : ℂ))) x
  = (a : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) x.
```

This is the existing complex Bochner orbital average, including at points
outside the orbit. The statement also gives the exact measure identity

```text
ν Ω = μG (K : Set G) / μH A
```

in `ℝ≥0∞`, and the actual complex Bochner integral identity

```text
(∫ x : LeftQuotient H, Ω.indicator (fun _ => (1 : ℂ)) x ∂ν)
  = (((μG (K : Set G)).toReal / a : ℝ) : ℂ).
```

No measure has been normalized or chosen: the Haar measures and every
compatible `ν` remain universally quantified. There is no normality
hypothesis on `H`, no quotient-measure uniqueness premise, and no prescribed
value for `μG K`. The hypotheses and conclusions concern the existing
quotient and averaging definitions without changing their imported modules.

The proposed derivation uses that the projection is continuous and open.
Closedness of `H` and compactness of `K` make `A` compact, while openness of
`K` makes `A` open. It contains the identity, so Haar positivity and
finiteness on compact sets give its positive finite mass. At a coset in
`Ω`, choose a representative in `K`. Its orbital integral is the integral
of the indicator of `A`, since `K` is a subgroup. Changing to another
representative uses right translation in `H` and right invariance of `μH`.
Outside `Ω`, the fiber indicator vanishes. This gives the separate
pointwise averaging argument. The indicator of `K` is continuous with
compact support, so the two compact-test compatibility fields apply to it.

The proof successor should route the mass identity through the stronger
`Langlands.QuotientIntegration.CompactOpenOrbitMeasureStatement` in
`Langlands.Analysis.Local.QuotientCompactOpenOrbitStatement`, after that
statement and its needed proof are accepted and published. Specialize its
restriction-measure equality to `g = 1` and evaluate on the whole quotient:
the actual restricted ambient measure has mass `μG K`, and its subgroup
factor is `μH A`. This yields the displayed ratio without another
measure-extensionality proof. Haar positivity and finiteness, or the
existing compatible-orbit mass lemmas, give the positive finite quotient
mass. The indicator integral then follows from the measure ratio and
`ENNReal.toReal` for positive finite masses. The restriction identity alone
does not prove the pointwise averaging identity; the separate right-Haar
argument remains necessary.

These identities provide generic normalization infrastructure for compact
quotient tests. They do not construct Whittaker functions, perform Kirillov
lifting or a last-row decomposition, or establish JPSS analyticity.
