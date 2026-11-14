# Constructing the Levi presheaf from restriction stability

This internal construction separates categorical coherence from the remaining
geometric base-change theorem. `RestrictionStable P` is the explicit condition
that the published actual subgroup restriction `restrictImage` preserves
`IsLeviImage` on all scheme tests over `S`. It uses exactly the existing
relative-Levi predicate and the existing all-test image equality. It does not
assert that stability holds for an arbitrary group scheme.

Given this condition, `LeviImage.restrict` restricts a Levi image by the same
actual pullback and ambient comparison as `restrictImage`. Its underlying
subgroup functor is definitionally that restriction. The identity and
composition equalities follow by subtype extensionality from the already proved
equalities for all subgroup functors.

`moduliFunctorOfStability` assembles these maps into a contravariant functor on
`Over S`, with values in `Type (u+1)` and object values the actual `LeviImage` of
the pullback of `P`. Its premise remains explicit. This module does not define
the unconditional moduli functor requested by the host task.
`moduliInclusionOfStability` forgets the existence of a Levi presentation as a
natural transformation into `subgroupPresheaf P`.

`leviConjugationAction r T` defines a left action of the actual group `U(T)` on
the Levi images in `P_T`. It applies the existing Levi-image conjugation to the
actual point obtained by pulling `r(g)` into `P_T`. The existing ambient
isomorphism transport preserves the actual relative-Levi presentation.
Multiplicativity of `pulledBackPointHom` and the all-test conjugation laws give
the action laws. This action needs no radical hypothesis: a supplied radical
is one permitted choice of `r`. Given stability, `LeviImage.restrict_smul`
proves that this action commutes with restriction, by the previously established
subgroup conjugation naturality.

`ModuliRepresentation.restrictionStable` proves that the already defined
representing correspondence implies the named stability condition. For a Levi
value on `M`, its inverse image under `pointsEquiv M` is an actual point of the
representing scheme. Restrict that point along `a : T → M`; the correspondence's
existing naturality identifies its resulting Levi image with `restrictImage`.
This is a consequence of a supplied representation and is not used as a proof
of unconditional stability or as an existence assumption in the torsor target.

All schemes remain in one arbitrary universe `u`. These definitions and helpers
are internal consequences of the published image, subgroup restriction,
conjugation and representing-correspondence APIs; they introduce no new
geometric assertion or axiom.
