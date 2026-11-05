# Ring-denominator pairs and the actual localization structured arrow

This construction implements the objects and maps used in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.III.1, example 3, printed page 252 / one-based PDF
page 258. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source page was read directly. The older-edition supplementary source
`renard-2010-corrections-complements`, PDF pages 18–19, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
also checked; no change to this example was found there. This is not an
exhaustive errata audit.

All declarations are in `Langlands.Renard.RingLocalization`. `RingPair`
consists of an actual `CommRingCat` object and an actual denominator
submonoid. `Hom` consists of a unital ring homomorphism and the proof that
it carries each designated denominator into the target's designated
submonoid. Identities and composition are the actual ring-map operations;
the category laws follow by equality of the underlying ring maps.
`forgetToCommRing` forgets the submonoid and retains those maps.

`localRingProperty` says exactly that each designated denominator is a
unit in its ring. `LocalRingCat` is its actual full subcategory, and
`localRingInclusion` and `localRingInclusionFullyFaithful` are Mathlib's
inclusion and fully faithful structure. In particular its morphisms are
all the ambient denominator-preserving ring maps between local objects.

For `A : RingPair`, `canonicalPair A` uses the actual ring
`Localization A.denominators` and designates the image of the original
submonoid under the actual `algebraMap`. The source leaves the denominator
submonoid of the localized pair implicit; this image is the internal
choice that makes the categorical construction well typed for all its
targets. Designating all units instead would change the factor problem:
a target may designate only some of its units, whereas only the image of
the original denominators is required to be preserved by the given map.
The image is a submonoid, and Mathlib's `IsLocalization.map_units` shows
that every one of its elements is a unit. This gives
`canonicalLocalObject A`. `canonicalRingMap A` is the actual `algebraMap`,
whose preservation law is membership in that image.
`canonicalStructuredArrow A` is its actual `StructuredArrow` for the
local inclusion. `canonicalRingMap_apply` is definitional equality.

For an actual local object `N` and ambient map `f : A ⟶ N.obj`,
`canonicalFactor A N f` is constructed using `IsLocalization.lift`.
The local property of `N` and denominator preservation by `f` give the
required invertibility of the denominator images. For each element of
the designated image in the source localization, its original
denominator witness and `IsLocalization.lift_eq` prove that its image
under the factor still belongs to the designated target submonoid.
`canonicalFactor_algebraMap` is this lift's evaluation law on elements
of the original ring. `canonicalLocalObject_subsingleton` reuses
`IsLocalization.subsingleton` to retain the source's zero-denominator
boundary: if zero belongs to the denominator submonoid, the actual
localized ring is subsingleton. No nontriviality or integral-domain
hypothesis is present.

The carrier universe `u` is arbitrary and fixed for the ambient category:
objects form `Type (u + 1)`, their rings have carriers in `Type u`, and
maps form `Type u`. The localization has the same carrier universe.
This construction does not shrink a larger ring into this universe and
does not assert an independent-target-universe comparison. Explicit
universe raising and its comparison, if needed by a consumer, remain
separate obligations. No smallness, finite-generation, dimension,
faithful-action or additional coefficient hypothesis is used.

The category implementation, full-subcategory packaging, designated
image choice and factor candidate are internal derived formulations of
the source example. This unit constructs them and proves their short
intrinsic laws. It does not assert categorical factorization, uniqueness,
initiality, a reflection functor or an adjunction. After these definitions
are actually published, a separate Prop-valued statement should require
`canonicalRingMap A ≫ localRingInclusion.map g = f`, unique `g`, and
`Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow A))`
or an equivalent actual initiality proposition. Its exact proof remains
a separate task. No completion of A.III or the whole book is claimed.
