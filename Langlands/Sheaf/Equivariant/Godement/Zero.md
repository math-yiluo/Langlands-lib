# The equivariant sheaf of arbitrary stalk-valued sections

Author: Worker 61. Reuses Worker 13's published transport categories and
equivariant sheaf interfaces.

For a commutative ring `R`, `zeroSheaf F` assigns to an open `U` the actual
module `StalkSections F U` of all families `s(x) in F_x` for `x in U`.
There is no continuity condition on such a family. Its map along a label
`g : U -> V`, `stalkSectionsPull`, sends `s` to the family whose value at `x`
is the pullback of `s(g x)` along the constructed stalk map; it is linear
because each stalk map is. `zeroPresheaf` packages these maps; its identity
and composition laws follow from the proved stalk-transport identities, and
`stalkPull_one_section` evaluates the identity transport on a family.
`zeroUnderlyingIso` identifies the underlying ordinary presheaf with Mathlib's
dependent-function presheaf after forgetting module structure. `zero_isSheaf`
then derives the module-valued sheaf condition from Mathlib's sheaf theorem
for dependent functions and the limit-reflecting forgetful functor.

`zeroMap` applies the actual induced map on stalks pointwise.
`zeroFunctor` packages these maps as an endofunctor of the published
equivariant sheaf category. `germFamily` sends a section to its germs, and
`coaugmentation` is the resulting natural transformation.
`germFamily_injective` uses Mathlib's sheaf section-extensionality theorem.
The instance `mono_coaugmentation` deduces categorical monicity without an
assumed embedding or an assumed cohomology comparison.

The space, coefficient ring and module carriers have universe `u`, and the
group has independent universe `uG`. The group acts by continuous
individual operators. This is an ordinary-topological construction; it does
not assert smoothness of arbitrary stalk families under a topological group,
nor the analytic equivariant étale specialization.

More precisely, this is an equivariant lift of the ordinary-topological
Godement construction. It is not yet the `nu_* nu^*` construction on the
equivariant topos in Berkovich section 1.5. For a one-point space, the
present construction retains the given group module; it does not introduce
the coinduction factors needed to resolve group cohomology. No flabbiness or
acyclicity in the equivariant category is claimed.

The source and exact reading extent are recorded in the companion
`Stalks.md`: Berkovich's unfinished 1995–1996 manuscript sections 1.4–1.5,
especially the Godement construction on printed page 10, and Harris 1999,
section 2, especially printed page 304. This module implements the
ordinary-topological family-of-stalks construction underlying that method.
Exactness, softness, and comparison with derived compact-support cohomology
remain separate theorem obligations.

Dependencies are the companion `Stalks` module, Mathlib's dependent-function
sheaves and module limits, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
