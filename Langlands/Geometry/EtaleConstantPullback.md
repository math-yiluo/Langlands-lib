# Constant sheaves under etale restriction

This internal construction compares actual constant sheaves on two small etale
sites. It uses Mathlib's sheafification and constant-sheaf functors and the
published `Langlands.Geometry.EtalePullback.restriction`, which precomposes a
sheaf with composition of etale structure morphisms.

## Parameters and scope

Let `X` and `Y` be schemes in universe `u`, let `f : Y ⟶ X` be etale, and
let `A : Type uA` carry a category structure with morphisms in universe `vA`.
Assume `HasWeakSheafify` for `A` on both small etale sites. The coefficient
category need not be a module category, and its universes are independent of
`u`. All the declarations below are in
`Langlands.Geometry.EtalePullback`.

Write `L = siteMap f : Y.Etale ⥤ X.Etale`. On objects, `L` composes the
structure morphism with `f`; on underlying scheme morphisms it is unchanged.
The etale hypothesis ensures that this gives objects of `X.Etale`. Its
continuity and cocontinuity, proved in the imported modules, provide the
sheafification compatibility used here.

## Construction and unit normalization

`constantPullbackIso f A` is a natural isomorphism

```
constantSheaf X.smallEtaleTopology A ⋙ restriction f A
  ≅ constantSheaf Y.smallEtaleTopology A.
```

For `M : A`, the source is restriction of the sheafification of the constant
presheaf with value `M`. The construction first uses the inverse of
`L.pushforwardContinuousSheafificationCompatibility` to identify it with the
sheafification of `L.op ⋙ const(M)`. It then applies `presheafToSheaf` to the
canonical constant-presheaf isomorphism supplied by
`Functor.constCompWhiskeringLeftIso`. This last comparison has identity
components. Both steps are natural in every coefficient morphism in `A`.
No output isomorphism is supplied as an assumption.

Let `ηX` and `ηY` be the constant-presheaf maps to their sheafifications.
`constantPullbackIso_hom_unit` proves

```
whiskerLeft L.op ηX ≫ ((constantPullbackIso f A).hom.app M).hom = ηY,
```

where `.hom` denotes the underlying presheaf map of a sheaf morphism.
Its proof uses the unit equation for sheafification
compatibility, cancels the compatibility isomorphism with its inverse, and
uses naturality of `toSheafify` for the constant-presheaf comparison.
`constantPullbackIso_inv_unit` proves the inverse equation
`ηY ≫ comparison.inv.hom = whiskerLeft L.op ηX` by cancellation and the
inverse identities.

`constantPullback_hom_ext` says that two sheaf maps out of a restricted
constant sheaf agree whenever their composites with the restricted
constant-presheaf unit agree. The proof transports the maps across the
comparison and applies the universal-property extensionality theorem
`sheafify_hom_ext`; it uses no assumption that the presheaf unit is an
epimorphism.

## Identity and composition

`constantPullbackIso_id` identifies the comparison for `𝟙 X`, at every `M`,
with the published identity-restriction comparison `restrictionId`.
`constantPullbackIso_comp` handles another etale morphism `g : Z ⟶ Y`,
assuming weak sheafification on `Z` as well. It proves

```
restrictionComp(f,g).hom.app(constantX(M)) ≫ comparison(g ≫ f).hom.app M
  = restriction(g).map(comparison(f).hom.app M) ≫ comparison(g).hom.app M.
```

Thus one comparison for the composite agrees with the successive constant
comparisons after the actual restriction-composition isomorphism. Both proofs
use `constantPullback_hom_ext`, the unit normalization, and naturality of the
original sheafification unit along the canonical over-category identity or
composition isomorphism. This checks the actual geometric identifications,
rather than treating the site functors as definitionally equal.

## Provenance and remaining work

The content is derived internally from the imported site restriction and
Mathlib's sheafification universal property, with no new literature theorem
claimed. This module supplies the constant-sheaf comparison and its identity
and composition equations. Its application to group actions and associated
invariant sheaves, compatibility with cover changes, arbitrary non-etale
inverse image, and the full Harris geometric and cohomological realization
remain separate constructions.
