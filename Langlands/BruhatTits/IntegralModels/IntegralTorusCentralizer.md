# Actual integral centralizers of the apartment split torus

This internal construction produces an actual smooth affine integral model
of a supplied generic torus centralizer inside a supplied smooth ambient
model. When the ambient model has geometrically connected fibres, the
centralizer model does as well. The generic arrow and integral inclusion
remain actual scheme morphisms throughout.

Let `R : Type u` be a domain with specified fraction field `K : Type u`.
Suppose `N : IntegralModel R K G` is smooth and
`A : IntegralSplitTorusData N i` is a compatible integral split torus for
`i : S.toGrp ⟶ G`. No maximality or closedness of `A.inclusion` is
required. The existing smooth-centralizer construction for a split torus
map over an arbitrary ring gives the chosen `centralizerGroup` and its
closed `centralizerIntegralInclusion` into `N.group`.
`centralizer_properties` records smoothness, closedness and full all-test
representation of `torusCentralizer A.inclusion`. Closedness inside an
affine ambient model gives affineness.

Base change preserves the full torus-centralizer functor. The generic
torus isomorphism in `A` and the specified ambient generic isomorphism
form the required commuting square, so `centralizer_generic_isRepresentedBy`
identifies the chosen generic inclusion with `torusCentralizer i` on all
scheme tests. For any specified representative `j : Z ⟶ G` of that
functor, uniqueness of represented subgroup functors gives
`centralizerGenericIso`. Its composite with `j` is the original generic
integral-centralizer inclusion. The resulting `centralizerModel` is smooth
affine, and `centralizerModelMap` is a closed compatible integral map
extending exactly `j`.

The published integrality theorem for compatible closed subgroup maps
then proves `centralizerModel_integralPoints_eq_comap`: a point of `Z(K)`
is integral exactly when its image under the specified `j` is integral in
`N`. Consequently its image in `G(K)` is precisely the intersection of
`N.integralPoints` with the actual full centralizer points. Neither point
identity is assumed.

If `N.group` has geometrically connected fibres, specialize the centralizer
representation to every field point of `Spec R`. The specialized ambient
group is smooth connected affine and the specialized acting group is a
split torus. The existing field theorem that split-torus centralizers in
smooth connected affine groups are connected applies without any
reductivity or maximality hypothesis. Testing all these field points
proves `centralizerModel_hasGeometricallyConnectedFibres`.

For the actual maximal-unramified integers of a nonarchimedean local field
`F`, let `C` be supplied building data and `D` supplied relative-component
model data. Suppose the full model has the prescribed character-kernel
one-fixer integral points for an apartment subset `Ω`. The constructed
integral apartment split torus factors into `D.neutral` by the preceding
neutral-root construction. `unramifiedNeutralCentralizerModel` applies the
general construction there, with generic group and arrow exactly
`C.centralizer.Z` and `C.centralizer.j`. It is smooth affine with
geometrically connected fibres, maps compatibly and closedly into the
neutral model, and has integral points exactly the preimage of the neutral
integral points under that original arrow. No boundedness or nonemptiness
of `Ω` is needed for this conditional construction.

Geometric connectedness of the supplied neutral model follows by comparing
its relative-component representative with the published smooth relative
identity component, whose geometric connectedness is already proved.
The comparison transfers that property to the specified representative.

The provenance is internal: the construction composes the existing
arbitrary-ring smooth centralizer, centralizer base change and transport,
uniqueness of represented subgroups, integrality through closed maps,
and field centralizer connectedness. It does not prove existence of the
ambient full fixer model, quasi-splitness of the generic group, an equality
with any torus norm-Iwahori subgroup, generation or finite index, or the
full zero-subgroup equality in `UnramifiedParahoricModelStatement`.
