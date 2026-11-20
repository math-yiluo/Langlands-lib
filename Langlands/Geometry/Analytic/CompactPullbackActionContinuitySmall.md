# Continuity on compact analytic pullbacks, with small affinoid spectra

`CompactPullbackActionContinuitySmallStatement` is the corrected form of
`CompactPullbackActionContinuityStatement` (module
`Langlands.Geometry.Analytic.CompactPullbackActionContinuity`) and replaces it.
It defines a proposition and does not prove continuity. The module also proves
the lemma `small_banachSpectrum_of_univLE`, which discharges the new hypothesis
in common universe settings.

## The statement

Fix a complete ultrametric normed field `K : Type u` and a group `G : Type z`
carrying a topology. The proposition begins with one explicit hypothesis:

* `∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R)`. The Berkovich
  spectrum of every presented affinoid algebra over `K` is small in the space
  universe `v`.

The rest is the body of the old statement, unchanged. Let `P → U`, `P → V`,
`U → B` and `V → B` form an actual categorical pullback (`IsPullback p q f g`) in
`LocalizedCategory.{u,v,v}`, with all four analytic spaces compact. Suppose `G`
acts by analytic automorphisms on `P`, `U` and `V`, through `σ`, `σU` and `σV`. The
actions on `U` and `V` are continuous in the Library's Berkovich test-triple sense
`IsContinuousAction`. If both projections are equivariant as full analytic
morphisms, that is `(σ h).hom ≫ p = p ≫ (σU h).hom` and
`(σ h).hom ≫ q = q ≫ (σV h).hom` for every `h`, then the action `σ` on `P` satisfies
`IsContinuousAction`.

As in the old statement, there is no topological-group instance, no action on `B`
and no pointwise description of pullback points. The pullback hypothesis is the
full localized universal property.

## The lemma `small_banachSpectrum_of_univLE`

Under `[UnivLE.{u, v}]` (the field universe is at most the space universe), every
`BanachSpectrum R` with `R : PresentedAffinoidAlgebra K` lives in `Type u` and is
therefore `v`-small (Mathlib's instance from `UnivLE`). This holds in particular
in `LocalizedCategory.{u, u, u}`. A consumer in that setting supplies the
hypothesis of the statement as `small_banachSpectrum_of_univLE`. The binder is
deliberately not `UnivLE.{u, v}` itself, which would ask for more.

## Why the old statement is replaced

`CompactPullbackActionContinuityStatement` has the same body without the
smallness hypothesis, so it covers independent universes `u` and `v`. The proof
route of Task 7765 works with pair charts. Take a chart algebra `A` of `U` and a
chart algebra `B` of `V` over a common chart algebra `C` of the base. The completed
affinoid pushout `A ⊗̂_C B` gives a pair-chart object (the Library's
`greatestChartPullback` in `SaturatedTopChartComparison`). The pullback's
universal property maps that object to `P` and identifies it with the patch of
`P` lying over the two factor charts. On the pushout algebra, the continuity of
the factor actions gives spectral estimates on the factor coordinates. These
estimates extend to every element by finite polynomial approximation
(`AffinoidPushout.spectralConvergesOn_of_factors` in
`AffinoidPushoutSpectralTests`), and from there to the charts of `P` inside the
patch, which are affinoid domains of the pair chart. For the pair chart to be an
object of `LocalizedCategory.{u,v,v}`, and so a test object for the universal
property, the construction needs
`Small.{v} (BanachSpectrum (A ⊗̂_C B))`. The Library's construction carries
this smallness as an instance hypothesis. The new binder asks for it for every
presented affinoid algebra. This requirement can fail when the field is not
`v`-small.

Example: let `K` be trivially valued with `K` not `v`-small. The closed disc of
radius `r < 1` has a spectrum in bijection with `[0, r]`, which is `v`-small. The
bidisc of radius `r`, the pair chart of two such discs over the point `M(K)`, is
not. For each `λ ∈ K` and a fixed `0 < t ≤ r`, `f(S, T) ↦ |f(S, λS)|_t` is a
point of the bidisc. Here `|·|_t` is the Gauss norm at radius `t` on power series
in `S`, which is `t` raised to the `S`-adic order because `K` is trivially valued. These
points are pairwise distinct: `T - μS` has value `0` at the point for `μ` and
value `t` at the point for any `λ ≠ μ`. So the spectrum has at least as many
points as `K`. The Library's own pullback theorem `smallFibreProduct_isPullback`
(`FibreProductLocalizedLimit`) likewise takes smallness as an explicit instance
hypothesis, there for the point space of the glued fibre product.

The old proposition is neither proved nor refuted. Its Lean text remains in the
Library unchanged. Its Markdown now marks it as not to be used as a target or as
a premise. Consumers that took it as a hypothesis (the conditional construction
of Task 7491) take this statement instead.

## Provenance

Internal. The statement was corrected at the operator's ruling on request
`a87ede08952355398eb14c6ddc2957c0` (option (a), by the procedure of standing
ruling 8). It is not a transcription of a cited source. The smallness hypothesis
is what the proof route of Task 7765 uses: the pair charts must be objects of the
localized category.
