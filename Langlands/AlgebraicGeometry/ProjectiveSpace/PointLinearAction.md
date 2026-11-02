# Linear action on actual rational points

For an arbitrary field `K` and natural number `n`, this module compares the
actual scheme action of a linear coordinate equivalence with its action on
vector-space projectivization. All rational points are actual morphisms
`Spec K → ProjectiveSpace K n` whose composite with the published structure
morphism is the identity. No algebraic-closedness assumption is used.

## Equivalence of actual rational points

`linearActionPointEquiv n e` sends a point `p` to the actual composite
`p ≫ linearAction K n e`. Compatibility of the scheme action with `Spec K`
proves that the composite remains over `Spec K`. The inverse is composition
with the action of `e.symm`. The scheme-action composition and identity laws
prove both inverse identities, including equality of the scheme morphisms.

## Representative-independent linear vanishing

`linear_vanishing_map_iff` states that a linear functional `ℓ` vanishes on the
representative chosen for `Projectivization.map e.toLinearMap e.injective v`
if and only if `ℓ.comp e.toLinearMap` vanishes on `v.rep`.

The linear equivalence sends `v.rep` to a nonzero vector. The projectivization
map formula identifies its line with the image line. The representative of
that line differs from `e v.rep` by multiplication by a unit of `K`.
Linearity and cancellation of that unit give the vanishing equivalence.
Consequently, the statement does not require the chosen representatives to
be preserved by the linear map.

## Exact comparison of actions

`pointLine_linearAction` proves

```
pointLine n (p ≫ linearAction K n e) hp' =
  Projectivization.map e.toLinearMap e.injective (pointLine n p hp).
```

Here `hp` and `hp'` express the two morphisms' equalities over `Spec K`.
The proof compares all linear vanishing tests. The actual scheme action
pulls back the homogeneous prime by polynomial substitution, whose value on
the polynomial of `ℓ` is the polynomial of `ℓ.comp e.toLinearMap`. The exact
incidence theorem for `pointLine` converts this membership to vanishing on
the coordinate-line representative. The preceding unit-scaling lemma
identifies it with vanishing on the representative of the projectivized
image. Equality of all these vanishing tests determines the line, by the
published injectivity of dual annihilators and the projectivization submodule
map.

`pointLineEmbedding_linearActionPointEquiv` packages this equality for the
injective map from the subtype of actual rational-point morphisms into
vector-space projectivization. Thus the two actions intertwine exactly.

## Provenance and scope

This is an internal comparison derived from `PointLines`, `LinearAction` and
Mathlib's actual projectivization map and representative formulas. It adds
no premise to the ambient geometric definitions. It does not claim that the
rational-point embedding is surjective, that pointwise equality determines
arbitrary scheme morphisms, or that a scalar coordinate action is globally
the identity. Automorphism rigidity, the torsion hyperplane bound and
`LargeLevelRepresentabilityStatement` remain separate obligations.
