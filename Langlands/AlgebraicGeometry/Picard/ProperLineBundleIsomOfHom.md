# Line-bundle Isom representability from line-bundle Hom representability

This module proves the conditional implication

```
ProperLineBundleHomRepresentabilityStatement.{u} →
  ProperLineBundleIsomRepresentabilityStatement.{u}
```

as `Picard.properLineBundleIsomRepresentability_of_hom`. It is the rank-one
analogue of the published coherent-family adapter
`CoherentSheaves.properIsomRepresentability_of_properHomRepresentability`: the
Isom scheme is the equalizer of the composite and identity maps between products
of two Hom schemes. The argument is the standard construction of Isom schemes
from Hom schemes (for example, Isom(L, M) as the closed subscheme of
Hom(L, M) × Hom(M, L) where both composites are identities). The Lean route,
described below, is internal to this project; it does not prove the Hom
statement, so the theorem is conditional on it.

## Comparison of Isom presheaves

Let `f : X → S` be flat, let `T` be a scheme over `S`, and let `L, M` be actual
line bundles on `T ×_S X`, that is, objects of
`PicardGroupoid ((relativeSpace f).obj T)`.
`PicardGroupoid.relativeIsomPresheafFamilyIso f L M` is a natural isomorphism

```
relativeIsomPresheaf f L M ≅
  FamilyGroupoid.isomPresheaf f ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M)
```

of presheaves on the entire slice of schemes over `T.left`, with all restriction
maps. It is the composite of:

1. `CategoryTheory.PseudofunctorPresheafHomTransport.presheafHomIso`, applied to
   the published strong transformation `PicardGroupoid.toFamilyStrongTrans f`
   from the actual relative Picard pseudofunctor to the coherent-family
   pseudofunctor, using that each of its components is fully faithful
   (`toFamilyStrongTransFullyFaithful`). This identifies the actual Hom presheaf
   of `L, M` with the actual Hom presheaf of their image families. Since the
   Picard groupoid's arrows are its isomorphisms, the former is the Isom
   presheaf defining `relativeIsomPresheaf`.
2. Whiskering by `T.iteratedSliceBackward.op` and `uliftFunctor.{u + 1}`, which
   matches the definition of `relativeIsomPresheaf`.
3. The inverse of the published `FamilyGroupoid.isomPresheafLiftIso`, which
   identifies the family Isom presheaf with the same whiskered, lifted presheaf
   of family-groupoid arrows.

## The conditional theorem

`properLineBundleIsomRepresentability_of_hom` assumes the Hom statement and
fixes the data `S, X, f`, properness, flatness, local finite presentation, `T`,
`L` and `M` of the Isom statement. For each of the four pairs `(L, M)`, `(M, L)`,
`(L, L)` and `(M, M)`, it applies the Hom statement and transports the resulting
affine locally finitely presented representation along the inverse of the
published `FamilyGroupoid.homPresheafIntrinsicIso`, getting a representation of
the full family Hom presheaf between the image families. (This is the same
transport packaged by `PicardGroupoid.relativeFamilyHomRepresentable_iff`; the
proof uses the underlying isomorphism directly.) The published closure lemmas
`IsAffineFinitePresentationRepresentable.of_isLimit_binaryFan`, applied to
Mathlib's binary product limit of type-valued functors, represent the two
products of Hom presheaves. The published `of_isLimit_fork`, applied to the
equalizer `FamilyGroupoid.isomPairForkIsLimit`, represents the family Isom
presheaf. Finally `of_iso` along `relativeIsomPresheafFamilyIso` gives the
representation of `relativeIsomPresheaf f L M` demanded by the Isom statement.

All declarations keep universe `u`, arbitrary base and parameter schemes, and
the full test slice. Properness and local finite presentation are used only
through the Hom hypothesis; the comparison isomorphism needs only flatness.
This module supplies no unconditional Hom or Isom representability proof and no
Picard atlas.
