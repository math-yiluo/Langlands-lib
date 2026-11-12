# Eventual representations of actual pullbacks at affine limits

This internal supporting unit combines scheme finiteness recovery, scheme
model descent, model uniqueness, and the universal property of actual
pullbacks. It does not prove model uniqueness or the full eight-property
limit-descent statement.

`exists_schemeRepresentation_of_presheafIso_of_modelUniqueness` assumes the
published `SpaceLimitModelUniqueness` proposition explicitly. For a
quasi-separated space with a locally finitely presented, quasi-compact atlas
over a stage of an arbitrary cofiltered affine scheme diagram, any
whole-presheaf scheme representation of its limit base change descends to a
scheme representation at a later stage. The representing scheme at that
stage is locally finitely presented, quasi-compact and quasi-separated over
the stage. No finiteness properties of the supplied limit scheme are
additional premises: `schemeFiniteness_of_presheafIso` recovers them, since
the limit is affine and the space hypotheses survive base change. The
presheaf isomorphism is lifted to a space isomorphism, and
`exists_schemeRepresentation_of_limit_of_modelUniqueness` supplies the
later scheme.

`baseChangePullbackSchemeIso` starts with an actual
cartesian square for a space pullback along a scheme. If the original map
becomes representable after a scheme base change, the base change of this
pullback space is represented by a scheme. The proof restricts the entire
presheaf square, uses the scheme Yoneda base-change isomorphism at the
scheme corner, and compares this square with the represented pullback
provided by representability. No assertion about representability at the
original base is used. The existential wrapper
`exists_presheafIso_of_representable_baseChange` retains just the existence
of that full presheaf isomorphism.

`exists_schemeTargetAtlas_of_modelUniqueness` combines these results for a
surjective etale target atlas. Its premises include quasi-separatedness and
the finite-presentation atlas condition on the actual pullback space, and
all three structural finiteness properties on the target atlas scheme.
Representability of the map is needed only at the limit. The conclusion is
a later-stage `SchemeTargetAtlas`, with all three structural finiteness
properties for both its scheme corners. Its target is the actual base
change of the supplied atlas. An arbitrary descended scheme representation
of the pullback suffices: `SchemeTargetAtlas.of_presheafIso` recovers the
actual projection by Yoneda fullness and transports the cartesian square.
Compatibility of the chosen representation with a preselected model
isomorphism is unnecessary.

All results are internal derivations from the named imported results.
Model uniqueness, the two finiteness conditions on the pullback, and the
geometric inputs just listed remain explicit; this unit does not assert
them for every morphism of finitely presented spaces.
