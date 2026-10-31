# Actual derived base change through compatible right resolutions

This internal extension computes the published `derivedBaseChangeMap` using
compatible right resolutions. It is the derived-category analogue of
`BaseChangeResolution`, using the actual morphisms rather than their
cohomology maps.

Let `g : Y ⟶ X`, `f : X ⟶ Spec R`, `f' : Y ⟶ Spec S`, and `φ : R ⟶ S`
satisfy `g ≫ f = f' ≫ Spec.map φ`. All objects have the same arbitrary
universe `u`. For natural-indexed module-sheaf complexes `K` and `L` and
a cochain map `t : K ⟶ g_* L`, `derivedResolutionBaseChangeMap` maps
sections of the integer extension of `K`, localized in the derived category,
to scalar restriction of sections of the integer extension of `L`.
Its specified composite uses the map induced by `t`, the inverse of
`derivedCompResolutionIso`, and the inverse of
`derivedResolutionPostcompIso` for the published base-ring sections
isomorphism. Thus every extension and localization comparison is retained.

If `ε : M[0] ⟶ K` and `η : g^*M[0] ⟶ L` are quasi-isomorphisms,
the pushforward of `η` is a quasi-isomorphism, and `t` commutes with
these augmentations over the actual pullback/pushforward unit, then
`derivedResolutionComparison_baseChangeMap` proves that the resolution
comparisons intertwine this specified map and `derivedBaseChangeMap`.
The coefficient `g^*M` must have vanishing positive higher direct images
along `g`, as required to define the latter morphism. No flatness of `φ`
or term acyclicity for relative sections is assumed.

The implemented proof first proves
`derivedResolutionComparison_inv_pushforwardComparison` for an arbitrary
coefficient morphism `M ⟶ g_*N`. Naturality of the generic resolution
comparison and `derivedResolutionComparison_compComparison` identify
the composite after cancellation with the canonical pushforward
isomorphism. The base-change formula then uses
`derivedResolutionComparison_inv_derivedCompIso` for exact scalar
restriction. The proof does not infer equality of derived morphisms from
their cohomology maps.

This is an internal derivation from the published resolution, composition,
and derived base-change interfaces; it does not restate an external source.
It does not assert invertibility of base change, scalar base change for
an arbitrary ring map, or the relative cube theorem.
