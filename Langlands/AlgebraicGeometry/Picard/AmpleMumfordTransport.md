# Ample Mumford presentations along homomorphisms of abelian schemes

This module transports the predicate `HasAmpleMumfordPresentation` (module
`AmpleMumfordBaseChange`) along a homomorphism `g : Y ⟶ X` of abelian schemes over
one base `T`, when the underlying morphism `hom g` is a closed immersion. It is
the fibre-transport step of `polarizationBaseChange`. There `g` is the comparison
between the successive and the direct base change of one abelian scheme, and its
underlying morphism is an isomorphism.

## Maps of self-products

- `hom_comp_structure g : hom g ≫ X.X.hom = Y.X.hom` and
  `unitSection_comp_hom g : unitSection Y ≫ hom g = unitSection X`. The first
  holds because `g` is a morphism over `T`. The second holds because `g`
  preserves the unit.
- `mumfordProductMap g : Y ×_T Y ⟶ X ×_T X` is the map of fibre products with
  `hom g` on both factors (`pullback.map`). `mumfordProductMap_fst` and
  `mumfordProductMap_snd` are its two projection identities.
  `mumfordProductMapOver g` is the same map as a morphism over `T`.
- `mumfordProductMap_addition g` states
  `mumfordProductMap g ≫ mumfordAddition X = mumfordAddition Y ≫ hom g`, that is,
  `g` commutes with the group laws. The proof uses `MonObj.comp_mul` and
  `MonObj.mul_comp` for the group homomorphism underlying `g`.

## Transport of the presentation data

Fix a line bundle `L` on `X`, a line bundle `B` on `T` with an evaluation
`e_X^* L ⊗ B ≅ O_T`, and a line bundle `M` on `X` with an evaluation
`N ⊗ M ≅ O_X`. Here `N` is the normalization of `L` from these data.

- `normalizedBundlePullbackIso` is the isomorphism
  `g^*(L ⊗ π_X^* B) ≅ g^* L ⊗ π_Y^* B`. It is built from the pullback-tensor
  isomorphism `LineBundle.pullbackTensorObjIso` (using `preservation`) and
  `π_X ∘ g = π_Y`.
- `pullbackUnitEvaluation` turns the given evaluation for `L` into an evaluation
  `e_Y^*(g^* L) ⊗ B ≅ O_T`. It uses `e_Y^* g^* ≅ (e_Y ≫ g)^* = e_X^*`.
- `pullbackNormalizedEvaluation` takes the evaluation `N ⊗ M ≅ O_X` and any unit
  evaluation `evaluationB'` for `g^* L`. It returns an evaluation `N' ⊗ g^* M ≅ O_Y`,
  where `N'` is the normalization of `g^* L` built from `B` and `evaluationB'`.
  It is composed of `normalizedBundlePullbackIso`, the inverse of the canonical
  pullback-tensor comparison (an isomorphism by `preservation`), `g^*` of the
  given evaluation, and `g^* O_X ≅ O_Y`.
- `mumfordBundlePullbackIso` identifies the pullback along `mumfordProductMap g`
  of the ordinary bundle `m^*(L ⊗ π^* B) ⊗ p₁^* M ⊗ p₂^* M` on `X ×_T X` with the
  corresponding bundle on `Y ×_T Y`, built from `g^* L`, `B` and `g^* M`. The
  isomorphism combines the pullback-tensor isomorphisms with the three
  identities for addition and the two projections above. Its source and target
  are written as explicit tensor expressions. By
  `mumfordFamilyOfLineBundle_forget`, these are the underlying bundles of the two
  normalized Mumford families.

## Main result

`hasAmpleMumfordPresentation_of_homomorphism` assumes
`[IsClosedImmersion (hom g)]`, actual dual data `hX`, `hY`, maps
`fX : X.X ⟶ dualScheme X hX` and `fY : Y.X ⟶ dualScheme Y hY`, and a compatibility
hypothesis `compat`. The hypothesis is a nonempty set of isomorphisms of ordinary
line bundles on `Y ×_T Y`. One side is the underlying bundle of the rigidified
pullback of `poincareFamily Y hY` along `fY`. The other side is the pullback along
`mumfordProductMap g` of the underlying bundle of the pullback of
`poincareFamily X hX` along `fX`. Under these hypotheses
`HasAmpleMumfordPresentation preservation square X hX fX` implies
`HasAmpleMumfordPresentation preservation square Y hY fY`.

Proof. Destructure the presentation of `fX` into `L, B, evaluationB, M,
evaluation`, the ampleness of `L` and the equality of `fX` with
`mumfordSchemeMapOfLineBundle`. The new presentation uses `g^* L`, the same `B`,
`pullbackUnitEvaluation`, `g^* M` and `pullbackNormalizedEvaluation`. Ampleness of
`g^* L` is `closedImmersionPullbackAmple` for the closed immersion `hom g`. For the
classifier equality, `eq_mumfordSchemeMapOfLineBundle_iff` reduces it to a
rigidified isomorphism. One side is the pullback of `poincareFamily Y hY` along
`fY`; the other is the normalized Mumford family of the new data. The chain of
ordinary isomorphisms is:

1. `compat`;
2. the pullback along `mumfordProductMap g` of the classifier isomorphism
   `mumfordSchemeMapOfLineBundlePullbackIso` for `X`, with its rigidification
   forgotten;
3. `mumfordFamilyOfLineBundle_forget` and `mumfordBundlePullbackIso`.

`RigidifiedLineBundle.nonempty_iso_of_forget_iso` (module `RigidifiedCarrierIso`)
turns this into a rigidified isomorphism. It applies because the first
projection `Y ×_T Y ⟶ Y` retracts the rigidifying section (`relativeSection_projection`).

## Scope and provenance

This is internal, derived infrastructure. The transported line bundles are
honest pullbacks of the given ones along `hom g`, and the evaluations are
explicit composites of canonical isomorphisms. No new line bundle, evaluation
or classifier is chosen. The result does not assert that `compat` holds for
arbitrary homomorphisms. `polarizationBaseChange` supplies it for the
base-change comparison from Poincaré-family compatibilities. Ampleness is
transported only along closed immersions.
