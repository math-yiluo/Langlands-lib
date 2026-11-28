# The twisted orbital integral of the compact open subgroup indicator

This module proves two theorems in `Langlands.TraceFormula`.
`unitTwistedOrbitalIntegral` proves `UnitTwistedOrbitalIntegralStatement`, the value
`μ(K) / μC(C ∩ K)` of the twisted orbital integral of the characteristic function of a
compact open subgroup `K` under the coset property.
`twistedCoset_of_unitTwistedOrbitalIntegral` is its converse: that value of the integral
implies the coset property. [Statement](UnitTwistedOrbitalStatement.md)

## Notation

`G` is a Hausdorff topological group with its Borel σ-algebra and a Haar measure `μ`,
`θ : G →* G` is continuous, `K` is a compact open subgroup with `θ k ∈ K` for `k ∈ K`, and
`δ ∈ K`. Put `C = twistedCentralizer θ δ`, the subgroup of `c` with
`c⁻¹ * δ * θ c = δ`, and let `μC` and `ν` be measures on `C` and on the left quotient
`C \ G` with `IsCompatible C μ μC ν`, as in the statement. Write `1_K` for the complex
indicator of `K` and

- `Ω = compactOpenQuotientOrbit C K`, the image of `K` in `C \ G`;
- `S` for the set of classes `C x` with `x⁻¹ * δ * θ x ∈ K`.

The descended function `twistedOrbitFunction θ δ 1_K` is the indicator of `S`; this
holds on representatives by definition (the private lemma
`unitOrbitFunction_eq_indicator`). The inclusion `Ω ⊆ S` holds because
`k⁻¹ * δ * θ k ∈ K` for `k ∈ K`, as `δ ∈ K` and `θ` maps `K` into itself.

## The mass of the image of `K`

The private lemma `compactOpenQuotientOrbit_measureReal` computes, for any closed
subgroup `H` of `G`, compatible measures `μ`, `μH`, `ν` and compact open subgroup `K`,

```text
(ν (image of K in H \ G)).toReal = (μ K).toReal / (μH (H ∩ K)).toReal.
```

The set `H ∩ K` is open in `H`, compact because `H` is closed, and contains `1`, so its
`μH`-mass is positive and finite. The indicator `1_K` is continuous, since an open
subgroup is also closed, and has compact support. By
`Langlands.QuotientIntegration.quotientAverage_compactOpen_leftCoset_indicator` at
`g = 1`, the quotient average `H x ↦ ∫_H 1_K(h x) dμH(h)` equals `μH(H ∩ K)` times the
indicator of the image of `K`. The integral formula in the compatibility hypothesis
then gives `μH(H ∩ K) · ν(image of K) = μ(K)`, and dividing by the positive mass
`μH(H ∩ K)` gives the formula. It is applied with `H = C`, which is closed by
`Langlands.TraceFormula.isClosed_twistedCentralizer` because `θ` is continuous and `G`
is Hausdorff.

## `unitTwistedOrbitalIntegral`

The coset property gives `S ⊆ Ω`: if `x⁻¹ * δ * θ x ∈ K` then `x = c * k` with `c ∈ C`
and `k ∈ K`, so `C x = C k` lies in `Ω`
(`Langlands.QuotientIntegration.leftQuotientMap_subgroup_mul`). Hence `S = Ω` and the
descended function is the indicator of `Ω`. The set `Ω` is open, hence measurable
(`Langlands.QuotientIntegration.isOpen_compactOpenQuotientOrbit`), and has finite
`ν`-measure (`Langlands.QuotientIntegration.IsCompatible.compactOpenQuotientOrbit_mass`).
Its indicator is therefore integrable with integral `(ν Ω).toReal`, which is
`μ(K) / μC(C ∩ K)` by the mass formula above.

## `twistedCoset_of_unitTwistedOrbitalIntegral`

The hypotheses are those of `UnitTwistedOrbitalIntegralStatement` with the same binders,
except that the coset property is replaced by the equation

```text
twistedOrbitalIntegral θ δ ν 1_K = (μ K).toReal / (μC (C ∩ K)).toReal.
```

No integrability hypothesis is made. The conclusion is the coset property: every
`x : G` with `x⁻¹ * δ * θ x ∈ K` is `c * k` with `c ∈ C` and `k ∈ K`.

The proof runs as follows.

- `S` is open: the function `C x ↦ x⁻¹ * δ * θ x` on `C \ G` is continuous because it
  descends a continuous function through the quotient map
  (`Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap`), and `S` is the
  preimage of the open set `K`.
- `Ω` is closed: it is compact
  (`Langlands.QuotientIntegration.isCompact_compactOpenQuotientOrbit`) and `C \ G` is
  Hausdorff because `C` is closed (`Langlands.QuotientIntegration.leftQuotient_t2Space`).
- By the mass formula the hypothesis says `∫ 1_S dν = (ν Ω).toReal`, and
  `0 < ν Ω < ∞`. The right side is nonzero, while the Bochner integral of a
  non-integrable function is `0`, so `1_S` is integrable. Hence `ν S < ∞`, the integral
  is `(ν S).toReal`, and `ν S = ν Ω`.
- Since `Ω ⊆ S` and `ν Ω < ∞`, `ν (S \ Ω) = ν S - ν Ω = 0`. The set `S \ Ω` is open, and
  a compatible measure is positive on nonempty open sets
  (`Langlands.QuotientIntegration.IsCompatible.isOpenPosMeasure`), so `S \ Ω` is empty
  and `S = Ω`.
- If `x⁻¹ * δ * θ x ∈ K`, then `C x ∈ S = Ω`, so `C x = C k` for some `k ∈ K`. Then
  `x * k⁻¹ ∈ C`, and `x = (x * k⁻¹) * k` is the required factorization.

## Source and scope

The forward theorem is the quotient-measure calculation underlying Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 17.8.3 and its proof,
printed pp. 464–465, in the setting of the twisted orbital integral (18.32), printed
p. 487. The source obtains the coset property from properness of the orbit map; here it
is a hypothesis.

The converse is derived from the same calculation and is not stated in these sources.
It covers situations in which the value of a twisted unit orbital integral is known
from a matching identity rather than from a coset decomposition, such as the comparison
of the units of the Hecke algebras in Arthur–Clozel, *Simple Algebras, Base Change, and
the Advanced Theory of the Trace Formula* (1989), Chapter I §4, Proposition 4.9,
printed p. 42. The theorem assumes the value `μ(K) / μC(C ∩ K)` for the supplied
measures; it does not compute or compare normalizations of these measures.
