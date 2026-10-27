# Group restriction of relative finite étale affinoid actions

Author: Worker 36.

This derived local construction restricts the group of an actual
algebraically finite étale affinoid object under a fixed norm-continuous
action. It retains the actual presented quotient algebra, its bounded
structural map, and every bounded arrow. For topological groups, it
compares the resulting continuous spectrum over the restricted base
with restriction of the original spectrum over its base.

## Relative restriction

Let `K` be an ultrametric normed field, `G` and `H` groups with
topologies, `f : H →ₜ* G` a continuous group homomorphism, and
`X : NormContinuousAffinoidAction K G`. The field and both groups have
independent universes. No continuity of the group operations is needed
for the relative algebra category.

`AlgebraicallyFiniteEtaleAffinoidActionUnder.restrict f X` first
includes the finite étale undercategory in `Under X`, then applies
`Under.post` to the published `NormContinuousAffinoidAction.restrict f`.
The structural bounded map is unchanged, so its original algebraic
finite étaleness proves that the restricted object lies in the
corresponding full undercategory under the restricted `X`.

`restrict_obj_baseMap` and `restrict_map_homMap` are reflexive
equalities identifying the actual structural and arrow maps.
Restriction is faithful: equality of the restricted arrows implies
equality of these bounded maps, and published relative extensionality
recovers equality of the original arrows.

`restrict_forget` proves that forgetting the structural arrow commutes
exactly with group restriction. `restrict_forgetAction` proves that
forgetting the action erases group restriction exactly, in the
published non-equivariant finite étale undercategory of `X.obj.V`.
Both are reflexive equalities of functors.

## Continuous spectra and the structural base map

Assume `G` and `H` are topological groups.
`NormContinuousAffinoidAction.spectrumRestrictIso f X` is the identity
homeomorphism on the actual bounded multiplicative spectrum, bundled
as an isomorphism of continuous `H` actions. The action on this spectrum
is inverse pullback. Its equivariance follows by evaluating a seminorm
on an algebra element and using `f (h⁻¹) = (f h)⁻¹`. The forward and
inverse evaluation lemmas state that its maps are the identity on
points. `NormContinuousAffinoidAction.spectrumRestrictionIso f` makes
these isomorphisms natural in every equivariant bounded map; naturality
holds by pointwise reflexivity.

`AlgebraicallyFiniteEtaleAffinoidActionUnder.spectrumRestrictionIso f X`
retains the structural maps to the base spectrum. On the source side,
it applies the spectrum-over-base functor after relative group
restriction and then `Over.map` of the base comparison just constructed.
On the target side, it applies `Over.post (ContAction.res TopCat f)` to
the original spectrum-over-base functor. These now have exactly the
same target over the restricted original base spectrum.

The comparison at each object is `Over.isoMk` of the identity on its
spectrum. Its commuting structural triangle and its naturality are
proved by extensionality down to points, where the equations are
reflexive because the actual bounded maps are unchanged. The two
relative evaluation lemmas identify both comparison directions with
the identity on seminorms. Continuity of spectra and of their arrows is
inherited from the published spectrum construction; the comparison
does not assume new continuity data.

As in the imported modules, the file installs
`NormContinuousAffinoidAction.topCatSelfForget` locally when spelling
`ContAction TopCat`. A downstream file spelling these continuous-action
targets can install that same local identity forgetful instance.

## Sources, provenance, and scope

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp. 1–3, defines
continuous analytic actions and morphisms that change groups along a
continuous homomorphism. Section 1.2, p. 3, uses relative equivariant
étale and quasi-étale objects and explains the associated site
constructions. These motivate this restricted local group-changing
construction. Registered literature:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The exact restriction functor and comparisons are internal derived
constructions, rather than numbered results attributed to the source.
They reuse the published actual norm-continuous action category,
finite étale undercategory and continuous spectrum-over-base functor,
and Mathlib's restriction, undercategory and overcategory operations.

This construction changes the acting group and retains the ground
field. It does not construct tensor base change, identify norm-orbit
continuity with the analytic automorphism topology, prove analytic
étaleness on every affinoid domain, or construct analytic atlases,
coverings, or the full equivariant sites. No injectivity or surjectivity
of `f` is assumed. The zero quotient, trivial valuation and empty
spectrum remain allowed; no completeness or common operator bound is
added.
