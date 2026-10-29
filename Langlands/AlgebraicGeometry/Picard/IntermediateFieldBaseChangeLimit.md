# Base change to an algebraic extension as a limit over finite intermediate fields

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingStatement`.
It is internal: it is not a Library statement. It formalizes step 2 of the route described for
that task (Stacks Project, proof of Lemma 33.15.1, tag 0BDB): for an algebraic extension
`Ω / K`, the field `Ω` is the filtered colimit of its finite intermediate fields `E`, so the base
change `X_Ω` of a `K`-scheme `X` is the cofiltered limit of the base changes `X_E`, with affine
transition maps. It also proves the hypotheses that the limit-spreading theorem
`exists_lineBundle_of_isLimit` of `Langlands.AlgebraicGeometry.Picard.LineBundleLimitSpreading`
needs for this diagram.

Throughout, `K Ω : Type u` are fields with `[Algebra K Ω]`, `X` is a scheme and
`p : X ⟶ Spec (CommRingCat.of K)`.

## The index category and the colimit of fields

- `FinIntermediateField K Ω` is the type of intermediate fields `E` of `Ω / K` with
  `FiniteDimensional K E`, ordered by inclusion (so it is a small category through its
  preorder). It is directed, because the compositum `E₁ ⊔ E₂` of two finite-dimensional
  intermediate fields is finite-dimensional, and nonempty (it contains `⊥`).
- `inclusionHom K Ω h` is the ring map `E ⟶ E'` of an inclusion `h : E ≤ E'`. The lemmas
  `inclusionHom_eq_id`, `inclusionHom_comp_inclusionHom`, `algebraMap_comp_inclusionHom`,
  `inclusionHom_comp_algebraMap` and `algebraMap_comp_algebraMap` record its compatibilities
  with identities, composition and the algebra maps `K → E → Ω`.
- `finIntermediateFieldDiagram K Ω` is the diagram `E ↦ E` in `CommRingCat`, and
  `finIntermediateFieldCocone K Ω` is the cocone of inclusions `E ⟶ Ω`.
- `isColimitFinIntermediateFieldCocone` (assuming `[Algebra.IsAlgebraic K Ω]`): this cocone is a
  colimit. The proof checks the colimit after the forgetful functor to types (which reflects
  filtered colimits) using `Types.FilteredColimit.isColimitOf'`: every `x ∈ Ω` lies in the
  finite-dimensional intermediate field `K(x)` (as `x` is algebraic, hence integral), and two
  elements of one `E` with the same image in `Ω` are equal.

## The cofiltered diagram of base changes

- `isPullback_pullback_map`: for `p : X ⟶ S`, `g : T ⟶ S`, `g' : T' ⟶ S` and `φ : T' ⟶ T` with
  `φ ≫ g = g'`, the map `pullback.map … (𝟙 X) φ (𝟙 S) : X ×_S T' ⟶ X ×_S T` and the second
  projections form a pullback square over `φ` (pullback pasting).
- `baseChangeDiagram X p : (FinIntermediateField K Ω)ᵒᵖ ⥤ Scheme` sends `E` to
  `pullback p (Spec.map (CommRingCat.ofHom (algebraMap K E)))` (exactly the form used in the
  target statement) and an inclusion `E ≤ E'` to the induced map `X_{E'} ⟶ X_E`
  (`pullback.map` with `𝟙 X` and `Spec` of the inclusion). `baseChangeDiagram_map_snd` states
  its compatibility with the second projections.
- `specDiagram` is the diagram `E ↦ Spec E`, and `baseChangeDiagramToSpec X p` is the natural
  transformation given by the second projections `X_E ⟶ Spec E`.
- `baseChangeCone X p` is the cone with apex
  `pullback p (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))` (the scheme `X_Ω` of the target
  statement) and projections the induced maps `X_Ω ⟶ X_E`.
- `isPullback_baseChangeCone_π_app` and `isPullback_baseChangeDiagram_map`: the projections
  `X_Ω ⟶ X_E` and the transition maps `X_{E'} ⟶ X_E` are base changes of `Spec Ω ⟶ Spec E` and
  of `Spec E' ⟶ Spec E` respectively (instances of `isPullback_pullback_map`).
- `isLimitBaseChangeCone` (assuming `[Algebra.IsAlgebraic K Ω]`): `baseChangeCone X p` is a
  limit cone. Since `Spec` turns the colimit `isColimitFinIntermediateFieldCocone` into a limit
  `Spec Ω = lim Spec E`, and every square formed by a projection `X_Ω ⟶ X_E`, the second
  projections and `Spec Ω ⟶ Spec E` is a pullback, Mathlib's
  `isLimitOfIsPullbackOfIsConnected` (limits over a connected category are stable under such
  cartesian natural transformations) gives the result. The index category is connected
  because it is cofiltered.

## The hypotheses of the limit-spreading theorem

- `Spec.map (CommRingCat.ofHom (algebraMap E Ω))` is surjective and scheme-theoretically
  dominant (instances), as a morphism between spectra of fields.
- Transition maps are affine (instance `IsAffineHom ((baseChangeDiagram X p).map f)`): they are
  base changes of morphisms of affine schemes.
- If `p` is quasi-compact (respectively quasi-separated), every `X_E` is quasi-compact
  (respectively quasi-separated) (instances): `X_E ⟶ Spec E` is a base change of `p` and
  `Spec E` is affine.
- `baseChangeCone_π_app_app_injective`: every projection `X_Ω ⟶ X_E` is injective on sections
  over every open of `X_E`. It is the base change of the scheme-theoretically dominant
  quasi-compact morphism `Spec Ω ⟶ Spec E` along the flat morphism `X_E ⟶ Spec E` (flat because
  `E` is a field), hence quasi-compact and scheme-theoretically dominant
  (`IsSchemeTheoreticallyDominant.of_isPullback`), and such morphisms are injective on sections
  (`Scheme.Hom.app_injective`).
- `baseChangeCone_π_app_surjective`: every projection `X_Ω ⟶ X_E` is surjective, as a base
  change of the surjective morphism `Spec Ω ⟶ Spec E`.
