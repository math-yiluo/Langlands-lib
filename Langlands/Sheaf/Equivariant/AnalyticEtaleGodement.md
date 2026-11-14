# Godement constructions for analytic étale G-sheaves

This internal construction specializes `TwistedOver.exactZeroFunctor` and
`exactCoaugmentation` to analytic étale `G`-sheaves, then implements the injective
retraction step in the planned acyclicity argument. It assumes neither a comparison
theorem nor acyclicity of any restricted injective sheaf.

The parameters are a complete ultrametric normed field `K`, a normed extension
field `L`, an analytic space `X`, point axioms `h` for the `L`-valued points, a
group `G` equipped with a topology and acting by analytic automorphisms through `ρ`, and a commutative
ring `R` in universe `max u (v + 1) uL`. The group is small in that universe, and
the distinguished lift system has admissible refinements. No Hausdorffness,
compactness, surjectivity of point projection, or continuity of the action is
assumed by this conditional construction; the group topology need not satisfy the
topological-group axioms.

`etaleGodementPoints` reindexes the actual family `etalePoints L h` by
`ULift` to the coefficient universe; at a lifted index its value is the original
point at the underlying index. This accommodates the generic Godement API,
which takes the index type and point fibers in the same universe.

`etaleGodementZeroFunctor` first includes the étale `G`-sheaf in module sheaves on
the twisted étale site, applies `TwistedOver.twistedZeroFunctor` for the actual
point family `etaleGodementPoints L h`, and takes the locally discrete part with
`LocalActionSystem.smoothCoreflector`. The twisted functor itself restricts to
the plain étale site, applies its degree-zero Godement functor, and induces back
along the site inclusion by right Kan extension. The existing smallness result
`etale_hasPointwiseRightKanExtension` provides this Kan extension.

`etaleGodementCoaugmentation` is the generic exact coaugmentation for the
inclusion and locally discrete coreflector adjunction. Thus its component is
the unit of that adjunction followed by the coreflector applied to the twisted
Godement coaugmentation. `mono_etaleGodementCoaugmentation_of_jointlyFaithful`
applies the generic monicity theorem under the explicit assumption that the
sheaf fibers of the original unlifted family `etalePoints L h` are jointly
faithful. Reindexing by `ULift` preserves this property by applying the original
hypothesis to the lifted representative of each point. This module does not
establish that assumption from the geometric hypotheses of either comparison.

For an injective étale `G`-sheaf `I`, `etaleGodementRetractOfInjective` assumes
its coaugmentation is monic and extends `id_I` across that monomorphism using
injectivity. This gives maps `I → C⁰(I) → I` whose composite is `id_I`; the
inclusion is the actual coaugmentation. Injectivity is required only in the
equivariant category.

The two `isZero_..._restriction_of_godementZero` theorems map this retraction
through `b^*` followed by either the actual compactly supported cohomology
functor or the actual ordinary étale cohomology functor, at any given natural
number degree `q`. A retract of a zero object is zero, so vanishing for the
restricted degree-zero Godement term implies vanishing for the restriction of
`I`. The functors preserve the retraction without needing to preserve
injectives. Both vanishing premises remain explicit. The ordinary variant
still depends on `h` through the Godement construction, even though the
ordinary cohomology functor itself does not.

The provenance is internal: every construction specializes published generic
Godement, local-action and injectivity APIs. No source theorem about softness,
local Galois cohomology, or compact-support acyclicity is asserted or proved.
Those analytic inputs, together with the required monicity, remain obligations
for the full comparison proof.
