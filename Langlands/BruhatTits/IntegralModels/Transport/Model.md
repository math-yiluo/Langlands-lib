# Transport of supplied KP models along a generic-group isomorphism

Module `Langlands.BruhatTits.IntegralModels.Transport.Model`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`: a supplied KP datum for `G`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, §4.1) is carried to `H` along an
isomorphism `f : G ≅ H` of group schemes over the field `K`. The source does not state this
transport separately. It reflects the remark that every assertion of KP Axioms 4.1.20 and
4.1.22 about a model concerns either its integral group scheme or its special fibre, both
unchanged here, or its generic points, which are carried along `f`.

## Construction

For an integral model `M` of `G` (an `R`-group scheme `M.group` with an identification
`M.genericIso` of its generic fibre with `G`), `M.transport f` keeps `M.group` and uses
`M.genericIso ≪≫ f`. Consequently:

- smoothness and connectedness of fibres are unchanged (`isSmooth_transport_iff`,
  `hasConnectedFibres_transport_iff`, by `Iff.rfl`);
- the generic point of a transported integral section is the `f`-image of the old one
  (`transport_integralPointMap`), so `(M.transport f).integralPoints` is the image of
  `M.integralPoints` under `rationalPoints.map f.hom` (`transport_integralPoints`).

`IntegralModel.Hom.transport` turns a model morphism over `g : G ⟶ H` into one between the
transported models over any `g'` with `g ≫ e'.hom = e.hom ≫ g'`; it keeps the integral
morphism. `Hom.transportId` is the case `g = 𝟙`, `e = e' = f`, `g' = 𝟙`.

`RelativeComponentModelData.transport` transports the full and neutral models and the
inclusion. The integral points of both are the `f`-images of the old ones. KP Axiom
4.1.20(4) carries over (`hasEqualComponentsForSimplyConnected_transport_iff`), because
`isSimplyConnected_iff_of_iso f` shows that `G` is simply connected exactly when `H` is.

`RelativeComponentModelHom.transport` keeps both integral morphisms. The neutral
special-fibre map is unchanged (by `rfl`). So the general special-fibre clauses, the parabolic
special-fibre image (KP 4.1.22(2)) and the reduction preimage (KP 4.1.22(4)) carry over
unchanged. The last one is proved by rewriting with the two definitional equalities of its
sides; a bare `Iff.rfl` is too slow for the elaborator.

`SpecialFibreQuotientData.transport` keeps the radical, the quotient and the projection, so
`IsReductiveQuotient` carries over by `Iff.rfl`. The positive subgroup
`(Q.transport f).positivePoints` is the `f`-image of `Q.positivePoints`. KP 4.1.22(7)
(`satisfiesPositiveRadicalClause_transport_iff`) then follows because the image map is
injective: `rationalPoints_map_injective_of_iso` shows this, and
`Subgroup.map_le_map_iff_of_injective` does the rest.

`IntegralTorusData.transport` takes a torus isomorphism `σ : S ≅ S'` and an inclusion
`j : S'.toGrp ⟶ H` with `i ≫ f.hom = groupHom σ.hom ≫ j`. It keeps the integral torus and its
inclusion, and composes the generic identification with `underlyingTorusIso σ` (`σ` read on
the underlying group schemes). The following carry over by `Iff.rfl`, because the special
fibre and its inclusion are unchanged:

- `IsClosedSplit`;
- the maximal split special fibre;
- the torus clause of KP 4.1.20(3);
- the maximal-split-tori assertion of KP 4.1.22(3) (`hasMaximalSplitTori_transport_iff`).

The generic character and cocharacter identifications change by `characterLattice.congr σ`
and `cocharacterLattice.congr σ`, by the two lattice lemmas `comapIso_trans_symm_apply` and
`cocharacterCongr_isoOfGroupIso_trans` (associativity of composition). Hence character and
cocharacter specialization through the transported torus are precomposed with the inverse
`σ`-transport (`transport_characterSpecialization`, `transport_characterSpecialization_symm`,
`transport_cocharacterSpecialization`).

## Helper lemmas

- `rationalPoints_map_comp_apply_of_ring`: functoriality of rational points over any ring.
  It is stated here so that the module does not need to import modules that have their own
  copy.
- `rationalPoints_map_injective_of_iso`.
- `underlyingTorusIso`: a commutative-group-scheme isomorphism regarded on the underlying
  group schemes. The Library's analogues are private.
