# Norm-continuous actions on presented strict affinoid algebras

Author: Worker 36.

This derived local construction uses the actual quotient algebras of
`PresentedStrictAffinoidAlgebra K`. Its full category contains every action
whose forward orbit of each algebra element is continuous in the quotient
norm, and all equivariant bounded algebra maps. The opposite category has
a functor to Mathlib's `ContAction TopCat G`, constructed from the actual
bounded multiplicative spectra and seminorm pullback.

The category, restriction, and inverse-pullback functor are internal
constructions. This file does not identify the norm-orbit condition with
Berkovich's analytic automorphism topology, construct analytic atlases, or
define an equivariant étale site.

## Objects and morphisms

`normContinuousAffinoidActionProperty K G` is the property on Mathlib
`Action (PresentedStrictAffinoidAlgebra K) G` requiring continuity of
`g ↦ X.ρ g a` for every actual quotient element `a`. Its full subcategory
is `NormContinuousAffinoidAction K G`. The field is an ultrametric normed
field in universe `u`; the group has its own universe `v` and a topology.
Continuity of group operations is needed only by the spectrum construction.
When `K` is complete the quotient algebras are complete. Neither the
category nor the spectrum argument adds a completeness assumption.

`ofAut` retains the specified homomorphism into bounded categorical
automorphisms. `actionAut` is Mathlib's group-action lift: its forward map
is `X.ρ g`, and its inverse is `X.ρ (g⁻¹)`. In particular,
`actionAut_ofAut` recovers the original homomorphism. No bounded inverse
is inferred from an algebraic bijection. `trivial` supplies an object
over every presented algebra, including a zero quotient.

`homMap` extracts an arrow's bounded algebra map; `homMk` admits every
such map satisfying the equivariance equations. `homMap_apply_action`
evaluates those equations on elements. Identities and composition are
inherited from Mathlib's action category and the full subcategory.
`hom_ext` makes equality of the retained bounded maps sufficient for
equality of arrows. The inclusion is full and faithful; `forget` to
presented algebras is faithful.

## Restriction

For a continuous group homomorphism `f : H →ₜ* G`, `restrict f` lifts
Mathlib's `Action.res` through the continuous-orbit full subcategory.
Each new orbit is an old continuous orbit composed with `f`. The actual
algebra, its norm, and each bounded arrow are unchanged, as expressed by
`restrict_obj_algebra`, `restrict_obj_apply`, and
`homMap_restrict_map`. Restriction is faithful.

## Continuous spectra

For a topological group, `spectrumAction` uses
`x ↦ BanachSpectrum.comap ((X.actionAut g).inv.toBoundedRingHom) x`.
The inverse is required to obtain a left action from contravariant
pullback. The existing automorphism action gives the identity and product
laws. `spectrumAction_apply` records its evaluation on an algebra element.

`spectrum` bundles this action as a `ContAction TopCat G`. Its continuity
proof applies the published `continuous_spectrumAction` theorem to
`X.actionAut` and `continuous_orbit`; it assumes no desired spectrum
continuity as input.

Mathlib's continuous-action category takes a specified forgetful functor
to `TopCat`. Here `topCatSelfForget` supplies exactly the identity functor,
with its compatibility equation proved by reflexivity. It is installed
locally in this file, and the exported definitions retain that specified
instance. A downstream file spelling the target as `ContAction TopCat G`
can use
`attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget`.

For an equivariant bounded map, `spectrumMap_equivariant` evaluates both
sides on an algebra element and applies the arrow's equivariance
equation at `g⁻¹`. `spectrumFunctor` therefore maps the opposite category
`NormContinuousAffinoidSpace K G` to continuous topological actions.
Its arrows are the actual continuous seminorm-pullback maps.
Functoriality follows by evaluation, since successive pullback is
composition of the underlying bounded maps. `spectrumFunctor_map_apply`
records that map explicitly.

Trivial valuations, nonreduced and zero quotients, empty spectra, and
zero presentation arity are retained. No common operator norm bound,
local compactness of the group, reducedness, or nonempty spectrum is
assumed.

## Sources and provenance

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
section 2.1, Definitions 2.1.2 and 2.1.11, printed/PDF pp. 7–8, supplies
the strict affinoid quotient and bounded-map context. Definitions 1.2.3
and 1.2.5 and Exercise 1.2.4, p. 4, supply the bounded multiplicative
spectrum with its evaluation topology. Registered literature:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp. 1–3, defines continuous
analytic group actions through the analytic automorphism topology,
equivariant morphisms, and group-changing morphisms with a continuous
group homomorphism. These passages motivate the present restricted,
fixed-field construction; the Lean category is not the full `G-An` of
that manuscript. Section 1.2's analytic étale and quasi-étale sites are
further obligations. Registered literature:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The exact norm-orbit category and functor are derived infrastructure,
not a numbered result attributed to either source. They reuse the
published actual affinoid construction, the existing inverse-pullback
automorphism action, the published joint spectrum-action continuity
proof, and Mathlib's action, full-subcategory, continuous-action, and
restriction APIs.
