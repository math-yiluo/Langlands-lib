# Bounded intertwiners on genuine smooth vectors

This internal supporting module transports the genuine smooth-vector
constructions of `SmoothDerivativeTopology` along a bounded map that is
*supplied* together with its intertwining hypothesis. It works with two bounded
complex representations `π : G →* (E →L[ℂ] E)` and `π' : G →* (E' →L[ℂ] E')` of
the same real Lie group `G`, modelled by `I : ModelWithCorners ℝ 𝔤 H`, and a
bounded complex-linear map `L : E →L[ℂ] E'` with
`hL : ∀ g v, L (π g v) = π' g (L v)` for every group element. The group, the two
model types `𝔤` and `H`, and the two normed carriers `E` and `E'` sit at five
independent free universes.

## Scope

Nothing here constructs an intertwiner, a globalization, or a Hilbert
completion: the map `L` (or the equivalence `e` below) and its full-group
intertwining hypothesis are inputs and are retained as explicit hypotheses.
Nor does the module establish that any subset of smooth vectors is dense, in the
derivative topology or otherwise; `dense_image_derivativeEquiv_iff` only says that
density of a subset *already given* is transported. In particular nothing here
asserts derivative-topology density of cuspidal vectors or the extension of a
Whittaker functional.

## Bounded intertwiners

- `isSmoothVector_map`, `map`, `map_apply`: the orbit map of `L v` is the real
  restriction of `L` composed with the orbit map of `v`, so `L` preserves
  genuine smoothness and restricts to a complex-linear map
  `smoothVectors I π →ₗ[ℂ] smoothVectors I π'`. No Lie group hypothesis is
  needed for this.
- `lieDerivative_map`: the actual real orbit derivative is transported,
  `lieDerivative I π' X (L v) = L (lieDerivative I π X v)` for smooth `v`. The
  proof is the real manifold chain rule `mfderiv_comp` at the identity applied to
  the same factorisation, with `ContinuousLinearMap.mfderiv_eq` for the bounded
  factor.
- `map_smoothLieDerivative`, `map_smoothIteratedLieDerivative`,
  `iteratedLieDerivative_map`: under `[LieGroup I ∞ G]`, the restricted map
  commutes with the published derived operators and, by induction on the word,
  with every genuine word derivative; on the underlying vectors,
  `iteratedLieDerivative I π' Xs (map v) = L (iteratedLieDerivative I π Xs v)`.
  The induction uses that genuine derivatives of smooth vectors are again smooth
  (the published `smoothLieDerivative`).
- `wordSeminorm_map_le`: hence
  `wordSeminorm I π' Xs (map v) ≤ ‖L‖ * wordSeminorm I π Xs v` for every word,
  by the operator-norm bound `le_opNorm`.
- `derivativeMapLinear`, `continuous_derivativeMapLinear`, `derivativeMap`: the
  induced map `DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π'` on
  the copies carrying the published derivative topology.
  `derivativeCoordinates_derivativeMapLinear` shows that each target derivative
  coordinate is `L` applied to the corresponding source coordinate.
- `isContinuousOnSmoothVectors_comp`: the finite-word continuity predicate
  pulls back along `map`: the published equivalence between that predicate and
  continuity on `DerivativeSmoothVectors` turns it into continuity, which is
  preserved by composing with the continuous `derivativeMap`.
- `map_smoothRepresentation`, `isWhittakerFunctional_comp`: `map` intertwines the
  smooth representations, so for an arbitrary subgroup `N` and character
  `χ : N →* ℂˣ` a Whittaker functional for `π'` pulls back to one for `π` with
  the same character.

## Continuous full-group equivalences

For `e : E ≃L[ℂ] E'` with `he : ∀ g v, e (π g v) = π' g (e v)`:

- `intertwining_symm`: the inverse also intertwines every group element.
- `smoothEquiv`, `smoothEquiv_apply`: restricting `e` and `e.symm` gives a
  complex-linear equivalence of smooth vectors.
- `derivativeEquiv`, `toSmooth_derivativeEquiv`: the same underlying
  equivalence is a continuous linear equivalence
  `DerivativeSmoothVectors I π ≃L[ℂ] DerivativeSmoothVectors I π'`; both
  directions are continuous by the coordinatewise argument above, applied to `e`
  and to `e.symm`.
- `dense_image_derivativeEquiv_iff`: for any specified subset `s`,
  `Dense (derivativeEquiv '' s) ↔ Dense s` in the derivative topologies.
- `isContinuousOnSmoothVectors_comp_iff`, `isWhittakerFunctional_comp_iff`: a
  functional `ℓ` on the smooth vectors of `π'` satisfies the finite-word
  continuity predicate, respectively the Whittaker predicate for `N` and `χ`,
  exactly when its pullback `ℓ ∘ smoothEquiv` does.
- `comp_eq_zero_iff`: `ℓ ∘ smoothEquiv = 0 ↔ ℓ = 0`, so pullback preserves
  nonvanishing.

## Provenance

The provenance is internal; no external source is translated. The results are
consequences of two facts about the published constructions.

*Chain rule.* For smooth `v` the orbit map of `L v` factors as the real
restriction of `L` after the orbit map of `v`, so the real manifold chain rule
(`mfderiv_comp`) transports the orbit derivative at the identity, and the
published smoothness of genuine derivatives lets the identity be iterated along
every word.

*Initial topology.* `DerivativeSmoothVectors I π` carries the topology induced by
`derivativeCoordinates`, the map sending a smooth vector to the family of all
its genuine word derivatives in the product `List 𝔤 → E`. A map into it is
therefore continuous as soon as every derivative coordinate of the composite is
(`continuous_induced_rng` with `continuous_pi`). By the chain-rule step each
coordinate of the induced map is `L` composed with the continuous source
coordinate `derivativeCLM I π Xs`, which gives continuity of `derivativeMap` and
of both directions of `derivativeEquiv`.

The module was prepared for the analytic comparison in Task 7293. The Lean
file sets `backward.isDefEq.respectTransparency false` for the chain-rule
proof, as the published `SmoothDerivative` does for its analogous proofs.
