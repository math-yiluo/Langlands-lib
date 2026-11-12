# The orbit relation of a group action as a quotient of its arrow relation

This internal helper supports the proof of `SmoothStabilizerActionQuotientStatement`. It
carries out the first quotient in the Stacks Project's proof of Proposition 101.28.9
(Tag 06QJ). That proof forms the quotient `R' = R/G` of the arrow space by the stabilizer
and shows that `R'` is an equivalence relation on `V` with flat projections. Here
`R'` is built as the canonical étale quotient of `G × V` by its arrow relation, using
the Library's smooth relation quotient theorem `smoothRelationQuotient` (the smooth case
of Bootstrap Theorem 80.10.1, Tag 04S6). The Stacks proof uses Bootstrap Lemma 80.11.7
(Tag 06PH) for this step; this proof does not. The smooth hypotheses let it apply the
smooth relation quotient theorem directly to the arrow scheme. The construction follows
the double-quotient pattern of the Library's Picard modules `SmoothDoubleQuotient` and
`ArrowQuotientEndpoints`; the endpoint monomorphism proof is adapted from the latter.

Let `G` be a group scheme over `S`, acting by `a` on `V`.

## Smoothness and finiteness of the inputs

- `isSheaf_etale_representable` says that a represented presheaf is a sheaf for the big
  étale topology, because étale covers are fppf covers.
- `smooth_snd` says that the projection `G × V → V` is smooth when `G` is smooth over
  `S`. It is a base change of the structure map of `G`.
- `locallyOfFiniteType_prod` says that `G × V` is locally of finite type over `S` when
  `G` is smooth and `V` is locally of finite type.
- `shear a` is the automorphism `(g, v) ↦ (g, g.v)` of `G × V`, with inverse
  `(g, w) ↦ (g, g⁻¹.w)`.
- `smooth_act` says that the action map is smooth when `G` is smooth. The action map is
  `shear a` followed by the smooth projection to `V`.

## The arrow relation and its quotient

`arrows a` is the arrow scheme `(G × V) ×_{V × V} (G × V)`, the kernel pair of the graph,
with projections `arrowsFst a` and `arrowsSnd a`. Its functor of points is the kernel
pair of the represented graph (`isPullback_arrows`).

- `arrows_isEquivalenceRelation` makes the arrow scheme a monomorphic equivalence
  relation on `G × V`. It uses the Library's `representedKernel_isEquivalenceRelation`.
- `arrows_hasSmoothProjections` says that both projections are smooth when the
  stabilizer is (`smooth_arrow_fst`, `smooth_arrow_snd`). The atlas condition then comes
  from `schemeRelation_hasSmoothProjections`.

`arrowQuotient a` is the canonical étale quotient sheaf of this relation, with quotient
map `arrowQuotientMap a` from `G × V`.

## Endpoints

`endpoint a` descends the represented graph to the arrow quotient, using
`quotientSheafDesc`. `arrowQuotientMap_endpoint` gives its factorization.
`endpoint_mono` proves that it is a monomorphism, adapting the proof of
`arrowKernelQuotientEndpoint_mono`. On the pointwise quotient presheaf the descended
map is injective, because the arrow relation is the whole kernel pair of the graph.
Étale sheafification preserves monomorphisms, and the target is already a sheaf.

`orbitFst a` and `orbitSnd a` compose the endpoint with the two projections of
`V × V`. On classes of points `(g, v)` they are `g.v` and `v`
(`arrowQuotientMap_orbitFst`, `arrowQuotientMap_orbitSnd`). `orbit_jointlyInjective`
says that together they are injective on every section type.

`arrowQuotientSpace a hF hD hAtlas` packages the arrow quotient as an algebraic space,
given its fppf sheaf property, representable diagonal and étale atlas.

## Smooth projections and the first quotient

`orbit_hasSmoothProjections` says that the two endpoints have smooth projections. The
argument applies `smoothProjectionAtlasOfSmoothCover` to the arrow quotient map, which
is smooth and surjective by the first quotient theorem. Along this map the endpoints
become the smooth action map and the smooth projection. Smooth-source descent is
supplied by `smooth_of_smooth_of_surjective_of_smooth_comp`.

`exists_orbitRelationSpace` is the main result of this file. Suppose `G` is smooth over
`S`, `V` is locally of finite type and the stabilizer is smooth. Then
`smoothRelationQuotient` applied to the arrow scheme makes the arrow quotient an
algebraic space `B`, with the following data:

- endpoints `s'` and `t'` to `V`, jointly injective on every section type;
- a map `q` from `G × V` with `q ≫ s'` the action map and `q ≫ t'` the projection;
- `q` is étale locally surjective (`isLocallySurjective_quotientMap`);
- `B, s', t'` have smooth projections.

These are the hypotheses of `actionQuotient_of_relationSpace` in
`SmoothStabilizerActionQuotientAssembly`. That module proves that `(s', t')` is an
equivalence relation and forms the quotient of `V` by it (the second quotient). It also
compares this quotient with every fppf quotient of the action.
