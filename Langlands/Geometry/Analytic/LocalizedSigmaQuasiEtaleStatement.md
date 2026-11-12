# Statement: quasi-étale and étale morphisms out of disjoint unions

Author: Worker 21.

This module states, without proof, that quasi-étale and étale morphisms can be
assembled on disjoint unions of analytic spaces. It contains one Prop-valued
definition,
`Langlands.Analytic.SaturatedAtlasPresentation.SigmaDescStatement`.

## The statement

`SigmaDescStatement : Prop`. Let `K` be a complete ultrametric normed field in
universe `u` and `J : Type z` an index type. Let
`Y : J → LocalizedCategory.{u, max z v, max z v}` be a family of analytic
spaces and `Z` an analytic space, and let `f j : Y j ⟶ Z` be morphisms. Write
`f̄ : ∐ Y_j ⟶ Z` for the morphism out of the disjoint union that restricts to
`f j` on the piece `Y j`. Formally, `f̄` is
`Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f`. The disjoint union
`localizedSigmaCofan Y` and its universal property `isColimitLocalizedSigmaCofan Y`
come from module `LocalizedDisjointUnion`. Then:

1. if every `f j` is quasi-étale (Library `quasiEtale`, module
   `QuasiEtaleSite`), so is `f̄`;
2. if every `f j` is étale (Library `etale`, module `EtaleSite`), so is `f̄`.

The universes are those of `LocalizedDisjointUnion`: the index type lives in
`Type z` and the spaces in the universe `max z v`, so that the disjoint union
is again a space of the same category.

Special case: `J` arbitrary, `Y j = Z` for all `j` and `f j = 𝟙 Z`. Then `f̄`
is the codiagonal `∐_J Z → Z`. Identities are quasi-étale and étale (the
`ContainsIdentities` instances in `QuasiEtaleSite` and `EtaleSite`), so the
statement gives that the codiagonal is quasi-étale and étale. The projection
`X_Σ → X` of Berkovich's space `X_Σ` (module `SetInducedSpace`,
`projectionHom X S`) is by definition this codiagonal for `Z = X.V`. The
intended use is to make `X_Σ` an object of the quasi-étale and étale sites of
`X`.

## Original sources and derived provenance

Berkovich, *Vanishing cycles for formal schemes* (1994), registered as
`berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed p.543: "We say
that φ is quasi-étale if for every point y ∈ Y there exist affinoid domains
V_1, ..., V_n ⊂ Y such that V_1 ∪ ... ∪ V_n is a neighborhood of y and each
V_i can be identified with an affinoid domain in a k-analytic space étale
over X." The condition is a condition at each point of the source, on affinoid
domains and neighbourhoods of that point.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, Definition 3.3.4, printed
p.63: a quasifinite morphism φ "is said to be unramified (resp. étale) at a
point y ∈ Y if there exists an open neighborhood 𝒱 of y such that the induced
morphism 𝒱 → X is unramified (resp. étale)". The text continues: "if φ is a
local isomorphism (i.e., φ is a local isomorphism at every point y ∈ Y), then
φ is étale."

Berkovich does not state the disjoint-union property separately. It is the
derived consequence of these definitions used implicitly in the 1996
manuscript, §1.2, printed p.4, where `X_Σ = ∐_{σ∈Σ} X_σ` is regarded as an
object of `X(G)_qét` (resp. `X(G)_ét`) through the morphism `γ`. Each piece
`Y j` is open and closed in the disjoint union. Affinoid domains and
neighbourhoods of a point of `Y j` in `Y j` are affinoid domains and
neighbourhoods in `∐ Y_j`, and the open neighbourhoods of Definition 3.3.4 may
be taken inside `Y j`. So both conditions at a point of `Y j` reduce to the
same conditions for `f j`.

## Scope

This is a `lean.statement`: nothing is proved here. The converse
implications are not stated.
