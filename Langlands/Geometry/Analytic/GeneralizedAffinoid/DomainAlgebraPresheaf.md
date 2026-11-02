# The retained algebra presheaves of full affinoid domains

Author: Worker 36.

Fix a complete ultrametric normed field `K` and an actual presented
positive-polyradius affinoid algebra `A`. The category `Domain K A` stores
an actual presented algebra and bounded structural map for every full
represented domain. Its arrows store the actual bounded restrictions.

`boundedPresheaf K A` sends a domain to that stored presentation and an
opposite domain arrow to its stored restriction. `banachPresheaf K A`
retains the underlying complete normed rings. `algebraPresheaf K A`
retains the underlying commutative `K`-algebras and the same restriction
maps. The category laws are the existing bounded identity and composition
laws. The displayed object and map equations are definitional.

Precomposing each presheaf with the opposite rational-to-domain inclusion
gives its existing rational counterpart literally. In particular,
`rational_algebraPresheaf` identifies both the values and restrictions
with those of the actual rational quotient-algebra presheaf.

`baseMapNat` and `algebraBaseMapNat` use the original structural maps from
the constant base algebra. Their naturality is precisely the stored
equation over the base in each domain arrow. On `whole K A`, the algebra
presheaf has the original algebra `A`.

This is an internal construction from the published full-domain category
and rational-domain bridge. It adds no assertion from the original
literature and reuses no private peer draft. It imposes no restrictions
on the positive radii or valuation and permits nilpotents, zero algebras,
and empty spectra. It makes no claim here that the stored algebra
presheaf is a sheaf or agrees with a sheaf extended by rational descent.
