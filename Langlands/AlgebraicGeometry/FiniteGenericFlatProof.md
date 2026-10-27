# Generic flatness for a finite morphism

`Langlands.AlgebraicGeometry.finiteGenericFlat` proves the unchanged Library
proposition `Langlands.AlgebraicGeometry.FiniteGenericFlatStatement.{u}`.
The universe `u` is arbitrary. For schemes `X Y : Scheme.{u}` and a morphism
`f : X ⟶ Y`, integrality and local Noetherianness of `Y`, together with
finiteness of `f`, imply the existence of a nonempty open `U` of `Y` such that
`Flat (f ∣_ U)`. Here `f ∣_ U` is Mathlib's actual scheme restriction.

## Implemented argument

The private helper `exists_flat_away` starts with a finite ring homomorphism
`φ : R →+* B`, where `R` is a Noetherian domain. After introducing the algebra
structure defined by `φ`, the finite module `B` is finitely presented over
`R`, by `Module.finitePresentation_of_finite`.

Set `K = FractionRing R`. The module `K ⊗[R] B` is the localization of `B`
at the nonzero divisors of `R` and is free as a vector space over `K`.
`Module.FinitePresentation.exists_free_localizedModule_powers` therefore
produces an element `r` in that multiplicative set for which
`LocalizedModule.Away r B` is free over `Localization.Away r`. Membership
in the nonzero divisors is equivalent to `r ≠ 0` because `R` is a domain.
The rank equality supplied by the descent theorem is unused.

The ring `Br = Localization.Away (algebraMap R B r)` carries the algebra
structure over `Localization.Away r` given by `localizationAlgebra`.
`IsLocalizedModule.linearEquiv`, followed by
`extendScalarsOfIsLocalization`, identifies `LocalizedModule.Away r B`
with `Br` as modules over `Localization.Away r`. Freeness transports across
this equivalence, hence `Br` is flat over that ring. Under this algebra
structure its algebra map is definitionally `Localization.awayMap φ r`.
Thus the helper proves flatness of that specific localized ring map.
It assumes neither injectivity of `φ` nor nontriviality of `B`.

The second private helper, `exists_flat_restrict_of_affine`, applies this
algebraic result to `f.appTop` when both schemes are affine. Its base ring
`Γ(Y, ⊤)` is a domain by integrality and is Noetherian by local
Noetherianness. `Scheme.Hom.finite_appTop` supplies finiteness of the
coordinate ring map. The resulting basic open `Y.basicOpen r` is nonempty:
on the reduced scheme `Y`, `basicOpen_eq_bot_iff` identifies an empty basic
open with the zero section, and `r ≠ 0`.

To prove flatness of the restriction, the helper uses
`IsAffineOpen.app_basicOpen_eq_away_map` to identify the map on sections
over this basic open with the induced map between the corresponding
localizations, up to an isomorphism of section rings.
`RingHom.Flat.respectsIso.isLocalization_away_iff` transports the algebraic
flatness result to those section rings. The inverse image of the basic
open is affine because `f` is finite and hence affine.
`morphismRestrict_appTop` then identifies the coordinate map of `f ∣_ U`
with this flat section map, again up to an isomorphism.
`HasRingHomProperty.iff_of_isAffine` turns its ring-map flatness into
flatness of the scheme morphism.

Finally, the public theorem chooses a point of the integral scheme `Y`
and an affine open neighborhood `U`. This neighborhood is nonempty,
integral and locally Noetherian, and `f ⁻¹ᵁ U` is affine. Applying the
affine helper to `f ∣_ U` produces a nonempty open `V` of `U`.
Its image `U.ι ''ᵁ V` is a nonempty open of `Y`.
`morphismRestrictRestrict` gives an isomorphism of arrows between
the successive restriction and the single restriction to this image.
Flatness respects this isomorphism, giving the required conclusion.

No integrality or nonemptiness of `X`, or surjectivity of `f`, is used.
In particular, the proof permits the zero coordinate algebra and the empty
source. No flatness or freeness witness is an added hypothesis: the
fraction-field vector space and finite-presentation descent construct
the needed free localization.

## Source and provenance

The mathematical target is the finite-morphism, locally Noetherian
specialization of the Stacks Project's
[Proposition 29.28.1, Tag 052A](https://stacks.math.columbia.edu/tag/052A),
with the module specialized to the structure sheaf and only the flatness
conclusion retained. The original proposition allows a finite type morphism
over any integral base and also proves finite presentation and assertions
about a given finite type quasi-coherent module. Those additional
conclusions are outside this theorem.

The implemented proof uses finite-presentation descent from Mathlib rather
than formalizing the original proof's finite affine cover and overlap
modules. Finiteness of the morphism makes the preimage of one affine target
open affine; Noetherianness ensures finite presentation of its finite
coordinate module. The private helpers are derived internal proof steps
for this target, not additional assumptions or separate source assertions.
Worker 667 implemented the proof from the route supplied by Worker 415
and the Mathlib interface leads checked by Worker 100 in the task contract.

The source is registered as `stacks-generic-flatness-052A-2026-10-25`.
The retained original is
`literature/Stacks Project — Generic flatness, Tag 052A (HTML snapshot 2026-10-25).html`,
SHA256
`bcd24c1b8433a6c2f781d325ed27ad9a7d73e302a226adf94ad03e376c5fd894`.
The full proposition and proof were read. The retained page has zero
comments, and the project and pinned Library have no source-specific
`notes/errata` directory. These checks concern the retained source;
they do not assert that no later correction exists.
