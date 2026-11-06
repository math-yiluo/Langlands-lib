# Properties of morphisms of algebraic spaces

Author: Worker 105.

This module defines properties of morphisms `f : X ⟶ Y` of algebraic spaces over a scheme `S`
that need not be representable: surjective, universally closed, separated, quasi-compact,
locally of finite type, proper and smooth morphisms, and morphisms with geometrically connected
fibres. It contains definitions only. They are inputs for Conrad's Corollary 5.6,
Proposition 5.8 and Theorem 5.9 (*Weil and Grothendieck approaches to adelic points*, printed
pp.16–17), which concern proper and smooth maps of algebraic spaces.

The source is the Stacks Project, registered as
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05` (folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`), chapters *Properties of
Algebraic Spaces* (Chapter 66) and *Morphisms of Algebraic Spaces* (Chapter 67).

## Conventions

The algebraic spaces and presheaves are those of `Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`.
`hom f` is the natural transformation underlying `f`. Fibre products `X ×_Y h_T` are Mathlib's
pullbacks `Limits.pullback (hom f) g` in the category of presheaves. Points and their topology
are `Points` and `pointTopology` from `Langlands/AlgebraicGeometry/AlgebraicSpace/SpacePoints.lean`.
`IsEtale`, `IsSurjective` (Basic) and `IsClosedImmersion` (Thickening) are the Library's
representable properties of transformations: representable, with every represented projection
étale, surjective or a closed immersion.

## Definitions

- `IsSurjectiveMorphism f`: the map of points `Points.map (hom f)` is surjective. Stacks,
  Chapter 67, Definition 5.2 (Tag 03ME): `f` is surjective if `|f|` is surjective.
- `IsUniversallyClosedMorphism f`: for every scheme `T` over `S` and every
  `g : h_T ⟶ Y.presheaf`, the projection `Points.map (pullback.snd (hom f) g)` from the points
  of `X ×_Y h_T` to the points of `h_T` is a closed map for the point topologies. Stacks,
  Definition 9.2 (Tag 03HI) tests all algebraic spaces `Z → Y`. Lemma 9.5 (Tag 03IT) shows that
  testing all schemes `Z` (condition (2)) is equivalent.
- `IsSeparatedMorphism f`: the relative diagonal `pullback.diagonal (hom f) : X ⟶ X ×_Y X` is a
  representable closed immersion. Stacks, Definition 4.2 (Tag 03HL): "`f` is separated if
  `Δ_{X/Y}` is a closed immersion".
- `IsQuasiCompactMorphism f`: for every affine scheme `T` over `S` and every
  `g : h_T ⟶ Y.presheaf`, there are a quasi-compact scheme `U` over `S` and an étale, surjective
  `h_U ⟶ X ×_Y h_T`. Stacks, Definition 8.2 (Tag 03HE) asks that `Z ×_Y X` be quasi-compact for
  every quasi-compact algebraic space `Z` over `Y`. Lemma 8.8 (Tag 03KG), condition (3), shows
  that affine schemes `Z` suffice. Chapter 66, Definition 5.1 (Tag 03E3) defines a
  quasi-compact algebraic space by a surjective étale map from a quasi-compact scheme.
- `IsLocallyOfFiniteTypeMorphism f`: there are schemes `U`, `V` over `S`, an étale surjective
  `a : h_U ⟶ X.presheaf`, an étale `b : h_V ⟶ Y.presheaf` and a morphism `φ : U ⟶ V` locally of
  finite type with `a ≫ hom f = h_φ ≫ b`. This is condition (8) of Stacks, Lemma 23.4
  (Tag 040Y), equivalent by definition to Definition 23.1 (Tag 03XF).
- `IsProperMorphism f`: separated, quasi-compact, locally of finite type and universally
  closed. Stacks, Definition 40.1 (Tag 03ZM): "`f` is proper if `f` is separated, finite type,
  and universally closed"; finite type means locally of finite type and quasi-compact
  (Definition 23.1).
- `IsSmoothMorphism f`: the same square condition as for local finite type, with `φ.left`
  smooth. Stacks, Definition 37.1 (Tag 03ZC) uses the equivalent conditions of Lemma 22.1 for
  the property "smooth", which is étale local on source and target.
- `HasGeometricallyConnectedFibres f`: for every field `K : Type u`, every `s : Spec K ⟶ S` and
  every `y : h_{Spec K} ⟶ Y.presheaf`, the points of the fibre `X ×_Y h_{Spec K}` form a
  connected space (`ConnectedSpace`, which includes nonemptiness). Every field extension of a
  field-valued point is again a field-valued point, so this is geometric connectedness of the
  fibres. It is the analogue of Mathlib's `GeometricallyConnected` for schemes.

## Derived content

The formulations through presheaf pullbacks and the choice among Stacks' equivalent conditions
are derived. Universal closedness tests only schemes. Quasi-compactness tests only affine
schemes and uses an explicit quasi-compact étale cover. Local finite type and smoothness use
the square condition with schemes. Each choice is one of the equivalent conditions cited
above. Fibre products of algebraic spaces are algebraic spaces (Stacks, *Algebraic Spaces*,
Lemma 7.2, Tag 04T9), so
the presheaf pullbacks are Stacks' fibre products; that fact is not formalized here. The
comparison with the representable notions already in the Library is not stated here. The
names are chosen here.
