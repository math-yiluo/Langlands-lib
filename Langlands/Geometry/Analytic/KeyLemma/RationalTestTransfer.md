# Finite tests control rational charts (Berkovich 1994, Proposition 6.1, rational case)

Module `Langlands.Geometry.Analytic.KeyLemma.RationalTestTransfer`, namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`. This module is a helper for the proof of
`QuasiEtaleAutomorphismLiftStatement`, the existence half of Berkovich's Key Lemma 7.2.

## Setting

`S` is a presented affinoid algebra over a complete non-archimedean field `K`. Let
`d : RationalChart K S` be a rational chart with denominator `g`, numerators `f_1, …, f_n` and radii
`r_1, …, r_n`. Its locus is `{x : |f_j(x)| ≤ r_j |g(x)| for all j}`. The structural map is
`d.baseMap : S → d.algebra`. "Tests" are finitely many elements together with a positive bound.
The estimates are made at points `y` of the bounded multiplicative spectrum of a test algebra `B`, a
presented affinoid algebra. A uniform estimate is the Library's
`BanachSpectrum.SpectralBound a r`, meaning `y a ≤ r` for every point `y`.

## Results

- `exists_transfer_tests d F hε` is Proposition 6.1 for a rational chart, in uniform form. Let `F`
  be a finite set of functions on the chart and `ε > 0`. There are a finite `D ⊆ S` and `δ > 0`
  with the following property, for every `B`, every bounded `old : d.algebra → B` and every
  bounded `b : S → B`. If `b s - old (d.baseMap s)` is uniformly at most `δ` for each `s ∈ D`,
  then `b` factors as `b' ∘ d.baseMap` for a bounded `b' : d.algebra → B`, and `b' h - old h` is
  uniformly at most `ε` for each `h ∈ F`.
- `exists_pointwise_transfer_tests d F hε` is the pointwise form. There are a finite `G ⊆ S` and
  `δ > 0` with the following property. Let `a₁, a₂ : S → B` be bounded and let `y` be a point of
  `B` with `a₁^*(y)` in the locus and `y (a₂ s - a₁ s) ≤ δ` for `s ∈ G`. Then `a₂^*(y)` is in the
  locus. Moreover, for all factorizations `a₁ = a₁' ∘ d.baseMap` and `a₂ = a₂' ∘ d.baseMap`,
  `y (a₂' h - a₁' h) ≤ ε` for each `h ∈ F`.
- The components are `exists_landing_tests` (the landing statement alone),
  `exists_function_tests` (one function) and `exists_finset_function_tests` (finitely many
  functions).
- The auxiliary lemmas are as follows. `exists_pos_le_denominator`: `|g| ≥ α > 0` on the
  compact locus. `exists_le_radii`: a positive lower bound for the radii.
  `apply_eq_of_apply_sub_lt` is the ultrametric isosceles property `y(b₂ − b₁) < y(b₁) ⇒ y(b₂) =
  y(b₁)`. `apply_pow_sub_pow_le`: `y(aⁿ − bⁿ) ≤ y(a − b) · max(y a, y b)ⁿ⁻¹`.
  `comap_comp_baseMap_mem_locus`: a map that factors through the chart sends every point into the
  locus.

## Relation to the literature

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994), §6, Proposition 6.1
(printed p. 558). The first case of its proof handles a rational domain `U = X(r f / g)`. If
`p(φ*f_j − ψ*f_j)` is bounded by `α r_j` and `p(φ*g − ψ*g) ≤ α/2`, where `α = min |g|` on `U`, then
`φ⁻¹(U) = ψ⁻¹(U)`. Moreover, a function `h` on `U` may be replaced by a nearby `h'/gᵐ` with
`h' ∈ A`, and then finitely many further tests on `h'` and `g` bound `|φ*h − ψ*h|`. This module
formalizes that rational case at the level of bounded algebra maps into an arbitrary presented
affinoid test algebra. The pair `(φ, ψ)` corresponds to `(a₁, a₂)`, or to
`(old ∘ d.baseMap, b)`. Berkovich's pseudo-distance condition corresponds to the spectral tests.
Two points differ from Berkovich. Landing is stated through the factorization: by the chart's
universal property (`RationalChart.represents`), a map into `B` lands in the locus exactly when it
factors through `d.algebra`. Also, the estimates are proved pointwise at each `y` and then
quantified over all `y`. Berkovich's reduction from general affinoid domains to finite unions of
rational domains (Gerritzen–Grauert) is not part of this module. In the Library that step is
available as the finite rational cover of a represented domain.

## Proof

*Landing* (`exists_landing_tests`). The tests are `g` and the `f_j`, with
`δ = min(α/2, α r)`, where `α` bounds `|g|` below on the locus and `r` bounds the radii below. At
`y` with `a₁^*(y)` in the locus, `y(a₁ g) ≥ α > δ`. By the isosceles property,
`y(a₂ g) = y(a₁ g)`. Then `y(a₂ f_j) ≤ max(y(a₁ f_j), δ) ≤ r_j y(a₁ g) = r_j y(a₂ g)`.

*One function* (`exists_function_tests`). The Library's
`RationalPresentation.dense_fractionSubalgebra` gives a fraction `z` with `gⁿ z = s'`, `s' ∈ S`, and
`‖h − z‖ < ε`. The tests are `{g, s'}` with
`δ = min(α/2, ε αⁿ⁺¹ / max(1, ‖s'‖))`, where `α = min(α₀, 1)`. Let
`D = a₂' z − a₁' z` and `c = y(a₁ g) = y(a₂ g) ≥ α`. The identity
`(a₁ g)ⁿ (a₂ g)ⁿ D = (a₁ g)ⁿ (a₂ s' − a₁ s') + a₁ s' ((a₁ g)ⁿ − (a₂ g)ⁿ)` and the power estimate
give `c²ⁿ y(D) ≤ c²ⁿ ε`, hence `y(D) ≤ ε`. The approximation errors `y(a_i' (h − z)) ≤ ‖h − z‖ < ε`
come from `BanachSpectrum.le_norm`. The ultrametric inequality then gives `y(a₂' h − a₁' h) ≤ ε`.

*Finite form and combination.* Induction on `F` takes unions of tests and minima of bounds. The
pointwise form joins the landing tests and the function tests. The uniform form takes
`a₁ = old ∘ d.baseMap`, which sends every point into the locus (`comap_comp_baseMap_mem_locus`,
via `RationalChart.range_comap_baseMap`). Landing at every point makes `b` satisfy `HasImageIn`. The
universal property `d.represents` gives the factorization `b'`, and the pointwise function
estimate at every `y` gives the uniform bound.
