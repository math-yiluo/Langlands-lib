# Functoriality and torus compatibility of the reductive Kottwitz map

This module proves `ReductiveKottwitzFunctorialityStatement` (Kaletha–Prasad, Lemma 11.5.1,
printed p. 430 / PDF p. 461) unconditionally, at every universe `u`. Let `F` be a
nonarchimedean local field and `k` a coefficient field with a scalar tower
`k → UnramifiedClosure F → SeparableClosure F`, where `SeparableClosure F` is a separable
closure of `k` and `UnramifiedClosure F` is normal over `k`. The theorem gives two facts about
the selected reductive Kottwitz homomorphism `reductiveKottwitz`:

- **Naturality.** For a morphism `f : H ⟶ G` of connected reductive `k`-groups and a point
  `x` of `H` with coefficients in the maximal unramified extension, the Kottwitz value of
  the image point `f(x)` is the image under `fundamentalInertiaMap ... f` of the Kottwitz
  value of `x`.
- **Torus compatibility.** On a `k`-torus `T`, the canonical inertia comparison
  `torusInertiaComparison` sends the reductive Kottwitz value of a point to its
  norm-and-valuation torus Kottwitz value `torusKottwitz`.

The point map is the actual coefficient evaluation `affinePointsTarget f` and the target map
is the selected `fundamentalInertiaMap`. No functoriality hypothesis is assumed.

KP says that "functoriality follows from Lemma 11.4.3", the domination of z-extensions along
a morphism. The Lean proof follows the same route through two published reductions, and every
input they need is a published proof.

## `reductiveKottwitzFunctoriality_of_existence`

This theorem assumes `ReductiveKottwitzExistenceStatement` and concludes
`ReductiveKottwitzFunctorialityStatement`. It applies `reductiveKottwitzFunctoriality_of_inputs`
from `ReductiveFunctorialityReduction` and discharges its other hypotheses with published
results:

- `FundamentalInertiaMapStatement` is `fundamentalInertiaMapStatement`.
- The algebraic fundamental-group comparison is `algebraicFundamentalGroupComparison`, and
  the map statement is `algebraicFundamentalGroupMap_of_comparison` applied to it.
- The torus inertia comparison is `torusInertiaComparison_proof`, and torus Kottwitz
  existence is `torusKottwitzExistence`.
- `SimplyConnectedDerivedKottwitzStatement` is `simplyConnectedDerivedKottwitz_of_norm_inputs`
  applied to the two fundamental-group results, `torusFundamentalComparison_proof`,
  `fundamentalInertiaMapStatement`, `torusInertiaComparison_proof` and
  `torusKottwitzExistence`.
- The z-extension domination hypothesis (KP Lemma 11.4.3) is exactly the body of
  `ZExtensionMorphismDominationStatement`, supplied by `zExtensionMorphismDomination`.
- The global torus naturality hypothesis comes from `torusKottwitz_natural_of_existence`
  applied to `torusKottwitzExistence`. That theorem does not use the separable-closure binder
  that the reduction's hypothesis carries, so it applies directly.

## `reductiveKottwitzFunctoriality`

This is the main theorem, with no hypotheses. It applies
`reductiveKottwitzFunctoriality_of_existence` to a proof of
`ReductiveKottwitzExistenceStatement`. That proof comes from the published reduction
`reductiveKottwitzExistence_of_remaining_inputs` (module `ReductiveMapRemainingInputs`),
whose four inputs are supplied as follows:

- `FundamentalInertiaMapStatement` is `fundamentalInertiaMapStatement`.
- `ZExtensionPointSurjectivityStatement` is
  `zExtensionPointSurjectivity_of_inducedTorusQuotient` applied to
  `inducedTorusQuotientPointSurjectivity`.
- `CentralTorusInertiaExactnessStatement`, the right exactness of
  `π₁(Z)_I → π₁(H)_I → π₁(G)_I → 0` for a central torus quotient, is
  `centralTorusInertiaExactness`.
- `ZExtensionCommonDominationStatement` (KP Fact 11.4.2) is proved inline from
  `zExtensionMorphismDomination`. For two z-extensions `z`, `t` of the same connected
  reductive group `G`, the proof applies morphism domination with `H = G` and `f = 𝟙 G`. This
  gives a z-extension `w` with maps `r` to `z` and `s` to `t`. The second compatibility
  `s ≫ t.p = w.p ≫ 𝟙 G` simplifies to `s ≫ t.p = w.p`.

The inline common-domination step is a local `have`, so the module adds no global name other
than the two theorems above.
