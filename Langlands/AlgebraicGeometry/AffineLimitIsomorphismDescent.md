# Isomorphisms after base change descend along affine limits

This is an internal derived helper for affine quotient descent. Let `D` be a
cofiltered diagram of affine schemes with supplied limit cone `c`, let `S` be
affine, and let `t` give compatible maps `Dᵢ → S`. Write `p : c.pt → S` for
their common composite. Let `a : X → S` and `b : Y → S` be locally of finite
presentation, with `X` and `Y` affine, and let `f : X → Y` satisfy `f ≫ b = a`.
If the base change of `f` along `p` is an isomorphism, its base change along
`Dᵢ → S` is an isomorphism for some `i`. All schemes and indices retain
arbitrary universe `u`.

The file uses the existing
`EtaleEquivalenceRelation.Action.TargetLimit` construction for the diagrams
`Dᵢ ×ₛ X` and `Dᵢ ×ₛ Y` and their limit cones. It does not supply a first
level of an equivalence relation, or assume any approximation statement.

`baseChangeMap` is the actual morphism
`Dᵢ ×ₛ X → Dᵢ ×ₛ Y` induced by the identity on `Dᵢ` and `f` on the second
factor. `baseChangeMap_fst` and `baseChangeMap_snd` give its projections.
`cone_π_fst` and `cone_π_snd` identify the projections of the base-change
cone legs, while `diagram_map_fst` and `diagram_map_snd` do the same for
transition maps. `baseChangeMap_naturality` and `cone_baseChangeMap` record
compatibility of the induced morphism with transitions and cone legs.
These equations follow from the pullback universal property.

`exists_inverse_factor` composes the inverse at the limit with the projection
to `X`. Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` factors this
map through one `Dᵢ ×ₛ Y`, retaining its equation over `S`.
This intermediate lemma needs finite presentation only of `a`, and does
not need affineness of `X`. Its source diagrams remain affine.

`exists_isIso_baseChangeMap` descends the two inverse equations. For the
first it compares the factor followed by `f` with projection to `Y`.
For the second it compares the level map followed by the factor with
projection to `X`. Both equalities hold after restriction to the limit.
Mathlib's
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` makes each true at
a later level. A cofiltered cospan gives one further level where both
equalities hold along the same transition. The factor and the projection
to that level lift to a map of pullbacks; their projection equations
give the two inverse identities.

`isomorphismLevel` chooses a witness of this proved existence statement.
`isIso_isomorphismLevel` supplies its isomorphism property.

The provenance is internal: the proof combines Mathlib's finite
presentation factorization and finite type equality theorems in
`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` with pullback
universal properties and cofilteredness. The factorization theorem is
the usual morphism part of limit descent, and the equality theorem carries
Mathlib's Stacks Tag 01ZC attribution. The new argument explicitly descends
an inverse and its equations; no unproved isomorphism-descent statement
is used.
