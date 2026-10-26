# Compact open quotient orbit averaging and mass: proof

Author: Worker 235.

`Langlands.QuotientIntegration.compactOpenOrbitMass` proves exactly the
published `Langlands.QuotientIntegration.CompactOpenOrbitMassStatement` from
`Langlands.Analysis.Local.CompactOpenOrbitMassStatement`. Its complete type
is that proposition, in its arbitrary universe `uG`, with every quantified
hypothesis unchanged. This module contains only that theorem. It adds no helper
lemma and changes neither the statement pair nor any imported published pair.

The provenance is internal. The proof uses the following accepted, published
results; those taking an element `g` are applied at `g = 1`:

- `compactOpenOrbitMeasure`, the proof of
  `CompactOpenOrbitMeasureStatement` in
  `Langlands.Analysis.Local.QuotientCompactOpenOrbitProof`;
- `quotientAverage_compactOpen_leftCoset_indicator`,
  `isOpen_compactOpenOrbitStabilizer` and
  `isCompact_compactOpenOrbitStabilizer` from the same module;
- `compactOpenQuotientOrbit` and its lemmas `isOpen_compactOpenQuotientOrbit`,
  `isCompact_compactOpenQuotientOrbit` and
  `IsCompatible.compactOpenQuotientOrbit_mass` from
  `Langlands.Analysis.Local.QuotientMass`.

The regular-measure extensionality argument is not repeated here. It is used
only through the published theorem `compactOpenOrbitMeasure`. Likewise, the
compact-continuous Weil identity in `IsCompatible` enters the numerical clauses
only through that theorem. Its proof applies the identity to continuous
compactly supported tests cut off by the indicator of `gK`. Here `g = 1`, so
the cutoff is the indicator of `K`.

No quotient measure is chosen or normalized. `μG`, `μH` and the compatible
`ν` remain the supplied measures. There is no normality premise on `H`, no
right-invariance premise on `μG`, and no uniqueness premise.

## Notation and the case `g = 1`

As in the statement, `q = leftQuotientMap H`, `Ω = q '' K`,
`A = {h : H | (h : G) ∈ K}` and `a = (μH A).toReal`. Applying
`compactOpenOrbitMeasure H hH μG μH K hK ν hν 1` produces three facts about
the set `S₁ = {h : H | 1⁻¹ * h * 1 ∈ K}` and the orbit
`C₁ = (fun k => q (1 * k)) '' K`:

```text
0 < μH S₁,   μH S₁ < ⊤,
ν.restrict C₁ = (μH S₁)⁻¹ • Measure.map (fun k => q (1 * k)) (μG.restrict K).
```

Simplification gives `S₁ = A`, `C₁ = Ω` and `{x | 1⁻¹ * x ∈ K} = K`. The
first two facts therefore become `0 < μH A` and `μH A < ⊤`.

## Geometry and positive finite masses

`Ω` is definitionally `compactOpenQuotientOrbit H K`. So
`isCompact_compactOpenQuotientOrbit H K hK` and
`isOpen_compactOpenQuotientOrbit H K` give its compactness and openness.
Since `A = S₁`, `isCompact_compactOpenOrbitStabilizer H hH K hK 1` and
`isOpen_compactOpenOrbitStabilizer H K 1` give the same for `A`. The positive
finite mass of `A` is the `g = 1` case of the first two restriction facts.
`IsCompatible.compactOpenQuotientOrbit_mass hν K hK` gives `0 < ν Ω` and
`ν Ω < ⊤`.

## Pointwise averaging

The restriction identity is not used for this clause. At `g = 1`,
`quotientAverage_compactOpen_leftCoset_indicator H μH K 1 x` states the
following for every `x : LeftQuotient H`:

```text
quotientAverage H μH ({y | 1⁻¹ * y ∈ K}.indicator 1) x
  = C₁.indicator (fun _ => ((μH S₁).toReal : ℂ)) x.
```

That helper computes the actual Bochner subgroup integral. At a coset in the
orbit it uses a representative in `K` and subgroup cancellation. At any other
point the fiber indicator vanishes. Rewriting with the three set identities
turns the left side into `quotientAverage H μH (K.indicator 1) x`. The right
side becomes `Ω.indicator (fun _ => (a : ℂ)) x`. A case split on `x ∈ Ω`
identifies that indicator with `(a : ℂ) * Ω.indicator 1 x`. The identity holds
at every point of the quotient, including points outside `Ω`.

## Mass ratio

Evaluating the `g = 1` restriction identity on `Set.univ` gives
`ν.restrict Ω univ = ν Ω` on the left. The pushforward map is continuous,
hence measurable, so `Measure.map_apply` applies to the measurable set `univ`,
whose preimage is `univ`. On the right this gives

```text
(μH A)⁻¹ * (μG.restrict K) univ = (μH A)⁻¹ * μG K
```

in `ℝ≥0∞`. Then `ENNReal.div_eq_inv_mul` rewrites this as the stated
`ν Ω = μG K / μH A`.

## Indicator integral

`Ω` is open, so it is measurable. By `integral_indicator_const`, the complex
Bochner integral of `Ω.indicator 1` with respect to `ν` is
`ν.real Ω • (1 : ℂ)`. Here `ν.real Ω = (ν Ω).toReal`. The mass ratio and
`ENNReal.toReal_div` turn this into `(μG K).toReal / (μH A).toReal`. This is
`(μG K).toReal / a` by the definition of `a`. `Complex.real_smul` and
`mul_one` give the stated complex value.

`ENNReal.toReal_div` holds without side conditions. The positive finite mass
of `A` is proved separately by the geometry clauses.

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. It constructs no Whittaker functions, performs no Kirillov
lifting or last-row decomposition, and establishes no JPSS analyticity.
