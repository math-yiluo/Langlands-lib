# The real Lie group of unitary unramified characters

*Worker 275 and Worker 806*

`Langlands.Plancherel.rationalUnitaryUnramifiedSubmanifold` proves
`RationalUnitaryUnramifiedSubmanifoldStatement.{u}`. For each nonarchimedean
local field `F`, connected reductive group `G` over `F` and integer basis
`b` of the valuation image, the proof constructs a smooth Lie group structure
on `Im X(G)` with its subspace topology. It proves that the inclusion into
`X(G)` is a smooth embedding for the real model of the published basis
chart, and that the prescribed imaginary exponential is a smooth local
diffeomorphism.

This is the real-submanifold component of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, § V.3.20, printed p. 116 / PDF p. 122. The registered source is
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof applies the principal complex logarithm in the basis coordinates
of the published statement.
[Statement and source correspondence](RationalUnramifiedComplexTorusStatement.md)

## Basis coordinates

Write `r = rationalImageRank G`. The restricted coordinate homomorphism
`coord : Im X(G) →* (Fin r → ℂ)` is a topological embedding whose values
have norm one in each coordinate. The lift `e` of the complex exponential
comes from the purely imaginary functional whose value at `b i` is
`(t i : ℂ) * I`. Its coordinates are `exp((a * t i) * I)`, where
`a = -log q` and `q` is the residue cardinality. The bound `q > 1`
gives `a ≠ 0`, so `phase t = e (a⁻¹ • t)` has coordinates
`exp((t i : ℂ) * I)`.
[Basis-coordinate lemmas](RationalUnitaryUnramifiedBasis.md)

## Angle charts and smooth group operations

At `x ∈ Im X(G)` put `c = coord x`. The ambient logarithm chart
acts coordinatewise by `z i ↦ log ((c i)⁻¹ * z i)` on the open set where
each ratio belongs to the complex slit plane. Its inverse is
`w i ↦ c i * exp (w i)` on the open strip `-π < im (w i) < π` in
each coordinate. At a unitary point every ratio has norm one, so the
logarithm has real part zero. Taking imaginary parts gives a chart on the
unitary subgroup with inverse `t ↦ x * phase t` on `(-π, π)^r`.
The inverse identity follows from the ambient logarithm chart and
injectivity of `coord`. Continuity of the inverse in the subgroup topology
follows by composing with `coord`, which induces that topology.

Each chart transition is smooth on its domain by composing the smooth
coordinatewise exponential and translated logarithm with the real-linear
inclusion of imaginary coordinates and projection to imaginary parts.
The same formulas show that `coord` is smooth and that a map into the
unitary subgroup is smooth if its composition with `coord` is smooth.
Multiplication in the coordinates is pointwise complex multiplication.
Inversion is pointwise complex conjugation because the coordinates have
norm one. These two smooth maps give the `LieGroup` structure.

## Smooth embedding and local diffeomorphism

For the inclusion, compose the ambient basis chart with the logarithm
chart centered at `coord x`. The smooth logarithm on its source and
smooth exponential inverse put this composite in the maximal smooth
atlas. In that chart and the unitary angle chart, the inclusion is
`t ↦ (t, 0)` under the continuous real-linear identification
`(t, s) ↦ (i ↦ (s i : ℂ) + (t i : ℂ) * I)`. This gives an immersion
with real complement `Fin r → ℝ`. The subgroup inclusion is already
a topological embedding, so it is a smooth embedding.

The exponential addition formula and injectivity of `coord` give
`phase (s + t) = phase s * phase t`. Near any `t₀`, the phase map is
therefore the translation `t ↦ t - t₀` followed by the inverse angle chart
at `phase t₀`. This proves local diffeomorphy there. Finally, `e` is
`phase` composed with the linear diffeomorphism `t ↦ a • t`, with inverse
`t ↦ a⁻¹ • t`. The basis-coordinate lemmas identify its composite with
the inclusion as the specified complex exponential.
