# Actual integral group models and their generic points

This module specializes Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Definition 2.10.1, printed p. 121 / PDF p. 152, to actual group schemes.
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Remarks 2.10.2–2.10.3 are at printed pp. 121–122 / PDF pp. 152–153.
The registered authors' corrections `kaletha-prasad-2024-corrections`
(1 November 2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 25, leave Definition 2.10.1 unchanged.

`IntegralModel R K G` is data over a domain `R` with specified fraction field
`K`. Its `group` is an actual `Langlands.GroupScheme (Spec R)`, namely a group
object in the category of schemes over `Spec R`. Its structural morphism is
affine, flat and locally of finite type. Affineness implies quasi-compactness,
so this is finite type. `genericIso` is a supplied group-scheme isomorphism
from the actual pullback along `Spec.algebraMap R K` to `G`. It identifies all
group operations, not just the underlying schemes. The record uses no
Henselian, discrete valuation, smoothness, connectedness or reductivity
assumption; these are unnecessary for its constructions. In the source's
variety setting the generic group is reduced and finite type; this interface
also permits generic groups outside that reduced setting.

`IsSmooth` is the separate proposition that this actual structural morphism
is smooth. It is not a field of `IntegralModel`.

The internal general construction `baseChangeSectionHom` applies to any map of
schemes `b : T → S`. It first restricts an `S`-section by precomposition with
`b`, then uses the inverse of the existing multiplicative pullback point
correspondence `baseChangeBasePointsEquiv`. Its projection and lift laws
identify the underlying scheme morphism, and its naturality is proved by
applying that same correspondence and the pullback projection formulas.

`integralPointMap` specializes this construction to the actual fraction-field
inclusion, then postcomposes with `genericIso`. Its evaluation law is the
explicit pullback lift followed by the specified isomorphism. `integralPoints`
is its image subgroup in the existing `rationalPoints G`, and
`mem_integralPoints` is exactly the existential image criterion. The map is
constructed from the supplied model; model existence is not assumed or proved.
An injectivity theorem, and the topological conclusions of Remark 2.10.3, are
outside this module.

`Hom M N f` supplies an actual integral group-scheme morphism together with
the square requiring its generic fibre to be `f` under the two supplied
identifications. This is Definition 2.10.1(2) with the group structures
retained; choosing `f` to be the identity gives part (3). The intrinsic point
naturality theorem follows from the general base-change naturality and that
square. It also proves that the generic homomorphism sends the integral image
into the integral image of the target model.

These point-map lemmas are internal categorical consequences of the
definitions, rather than additional results quoted from KP. No parahoric,
fixer, reduction-surjectivity, reductive-quotient or topology conclusion is
built into the model.
