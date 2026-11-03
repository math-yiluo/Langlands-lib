# Actual inverse images of full affinoid domains and finite covers

Let `K` be any complete ultrametric normed field, `A,B` actual presented
affinoid algebras over `K`, and `φ : BoundedAlgHom K A B` any bounded coefficient
map. For every full represented domain `U` of `A`, this internal construction
gives an actual full domain of `B` with exactly the spectrum inverse-image
locus. It also constructs the quotient transport map, the pullback of all actual
domain arrows, and pullback of actual finite full-domain covers. No
contractivity, rationality, strictness, nontrivial valuation, reducedness,
nonzero-quotient, or nonempty-spectrum hypothesis is imposed.

## The actual inverse-image representation

`represents_pullback` uses the existing constructed
`AffinoidPushout.algebra φ U.baseMap`. Its first quotient leg is a bounded map
from `B` to that algebra. The theorem proves that this actual leg represents
`BanachSpectrum.comap φ.toBoundedRingHom ⁻¹' U.locus` against every actual
presented affinoid test.

The inverse-image set is closed by continuity of the original coefficient
spectrum map. To prove its exact spectrum image, the pushout compatibility
equation first identifies the image of any quotient point under `φ` with the
original structural image of its second projection point. The latter belongs
to `U.locus`, so the first projection lies in the required inverse image.
Conversely, a point of `B` in that inverse image gives a point of `U.algebra`
with the same image in `A`, by the original exact-image property of `U`.
`AffinoidPushout.exists_point` constructs a point of the actual quotient with
this original first projection. That theorem uses the published common-field
point realization and the actual bounded pushout lift; no generic injectivity of
pushout spectra is assumed.

For the full universal property, let `ψ : B → R` be a bounded map to any actual
presented affinoid test whose spectrum image lies in the inverse-image locus.
Then `ψ.comp φ` has image in `U.locus`. The original full representation of
`U` factors it uniquely through a bounded map `β : U.algebra → R`. The
constructed bounded pushout lift of `ψ` and `β` gives the required map from the
actual quotient to `R`, and the first leg identity computes its structural
composite. For uniqueness, that first composite is supplied by the test
condition; the original uniqueness for `U` determines the second composite.
Separation by both quotient legs determines the whole map. The test algebra is
complete and ultrametric by its existing presentation over complete `K`.

`pullback φ U` stores this actual quotient, the first quotient leg, the exact
inverse-image locus, and the proved representation. `pullback_locus` and
`pullback_algebra` expose these exact choices.

## Original maps and all restriction arrows

`pullbackMap φ U` is exactly the second bounded quotient leg, from the original
stored algebra of `U` to the new actual algebra. The equation
`pullbackMap_comp_baseMap` is the original commuting bounded coefficient square,
proved by the pushout compatibility identity.

For an actual domain arrow `f : U → V`, `pullbackRestriction φ f` constructs
an actual arrow between the two inverse-image domains. Its algebra restriction
is the bounded pushout lift into the actual algebra of `pullback φ U`.
The two input maps are that domain's original first structural leg and the
composite `pullbackMap φ U` after `f.restriction`. Compatibility follows from
the original equation `f.comp_baseMap` and the preceding coefficient square.
The first lift identity supplies the required structural triangle over `B`.
`pullbackRestriction_comp_pullbackMap` is the second lift identity: the new
restriction commutes with the original quotient transport maps.

`pullbackFunctor` sends every actual full domain to this inverse-image domain
and every original arrow to this constructed changed restriction. Identity and
composition hold by the established uniqueness of actual domain inclusions.
This is a functor on the existing full-domain categories, with no assumed
existence of inverse-image domain objects or changed arrows.

`pullbackSpectrumMap` is the continuous comap of the original second quotient
leg. `pullbackSpectrumMap_over_base` proves its exact original coefficient
square on spectra by evaluating the bounded-map equation at every original
algebra element.

## Finite covers and provenance

For `c : Domain.FiniteCover U`, `c.pullback φ` retains the same finite index
size, replaces every member by its actual inverse-image domain, and uses
`pullbackRestriction φ (c.map i)` as the original covering arrow. A point in
the inverse-image target locus maps into `U.locus`; the original cover supplies
an index whose locus contains that image. The defining exact preimage loci
therefore prove covering for the new family. `pullback_obj` and `pullback_map`
expose the exact component choices. Empty finite covers and zero quotients are
retained by the same proof.

This is an internal consequence of the actual affinoid pushout quotient and
lift, compatible-point realization, and full-domain representation and
inclusion uniqueness. It makes no new original-literature attribution. The
module does not yet prove identities or composition comparisons between
successive coefficient changes, package a topological spectrum pullback limit,
construct unrestricted atlas restrictions, or define analytic and equivariant
sites. Those are further constructions using these actual inverse-image
objects, maps, and finite covers.
