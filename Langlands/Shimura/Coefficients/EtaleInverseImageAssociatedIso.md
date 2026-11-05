# Inverse image of associated torsor sheaves along arbitrary morphisms

This internal construction proves that, for a finite geometric torsor, the
product-sheaf base-change map from `EtaleInverseImageAssociated` is an
isomorphism along an arbitrary morphism of schemes. As a consequence, inverse
image of the associated (invariant) coefficient sheaf is naturally
isomorphic to the associated sheaf of the base-changed torsor, with explicit
formulas on invariant sections. Along the way it identifies the map for étale
morphisms with the existing étale comparison, proves a composition law, and
treats covers that have a section. All declarations are in namespace
`Langlands.Shimura.Coefficients`.

## Scope

The coefficient actions are arbitrary sheaf-valued actions; the constant
module specialization and the varying-system comparison are not constructed
here. No cohomology, derived inverse image or Shimura specialization is
asserted. These remain separate steps of the broader Harris task.

## Notation and inputs

Schemes, the commutative ring `R`, module carriers and groups lie in universe
`u`; module sheaves are on small étale sites. For a morphism `f`, write `f^*`
for the existing `inverseImage f R`, `f_*` for `directImage f`, and `P_f` for
`etaleObjectPullback f`. Let `c_f V F` denote the existing
`inverseImageProductSheafMap f R V F` from `f^*(productSheaf V F)` to
`productSheaf (P_f V) (f^* F)`. By definition it is adjoint to the product
sheaf of the unit followed by `directImageProductSheafIso`. Other inputs are
the existing `coverPullback`, `etaleProductSheafPullback`,
`inverseImageIsoRestriction`, `inverseImageComp`, `directImageComp`,
`etaleObjectPullbackComp`, `IsFiniteGeometricTorsor`,
`TorsorSectionSplitting` and its proof `etaleTorsorSectionSplitting`.

## Étale morphisms

Assume `[Etale f]`. The existing restriction/direct-image adjunction
`restrictionGeometricAdjunction` comes from the site adjunction
`siteMapPullbackAdjunction`.

- `siteMapPullbackAdjunction_counit_app` identifies its counit with the
  existing first fiber projection `etalePullbackProjection`.
  `restrictionGeometricAdjunction_unit_app_hom_app` states that its unit
  restricts sections along that projection.
- `etaleProductPullbackHom_projection` is the scheme-level identity
  comparing the existing étale product comparison with the base change of
  products; it is checked on both product projections.
- `restrictionGeometricUnit_etaleProductSheafPullback` states that the
  published `etaleProductSheafPullback` and `directImageProductSheafIso` have
  the same adjoint under the restriction adjunction.
- `inverseImageProductSheafMap_etale` states that `c_f V F` equals
  `inverseImageIsoRestriction` at the product sheaf, followed by
  `etaleProductSheafPullback` and the product sheaf of the inverse of
  `inverseImageIsoRestriction`. The proof compares adjoints, using the
  existing `inverseImageIsoRestriction_unit`.
- The instance `isIso_inverseImageProductSheafMap_etale` follows.

## Composition

For `f : Z ⟶ X` and `g : W ⟶ Z`:

- `inv_prodComparison_etaleObjectPullbackComp` is the scheme-level coherence
  of product comparisons for `P_{g ≫ f}`, `P_f`, `P_g` and the existing
  `etaleObjectPullbackComp`. It is checked after the invertible product
  comparison of `P_f ⋙ P_g`.
- `directImageProductSheafIso_comp` is the corresponding sheaf-level
  identity between the direct-image comparisons for `f`, `g` and `g ≫ f`,
  with `directImageComp` and restriction along `etaleObjectPullbackComp`.
- `inverseImageProductSheafMap_comp` states

  ```text
  inverseImageComp.hom ≫ c_{g ≫ f} V F
    = g^*(c_f V F) ≫ c_g (P_f V) (f^* F) ≫ coverPullback(e_V) ≫ Π(inverseImageComp.hom),
  ```

  where `e_V` is the component of `etaleObjectPullbackComp` at `V`. The proof
  compares adjoints under the composite adjunction. It uses the existing
  `inverseImageComposition_unit`, naturality of `directImageComp`, unit
  naturality, `coverPullback_natural`, the defining adjoints of the three
  base-change maps, and `directImageProductSheafIso_comp`.

## Covers with a section

Let `S W : Scheme.{u}`, `f : W ⟶ S`, and let `t : S.Etale` be terminal.

- `terminalProdIso ht U : t ⨯ U ≅ U` is the second projection, and
  `productSheafTerminalIso R ht` identifies `productSheaf t` with the identity
  functor.
- `lift_inv_prodComparison`, `directImageProductSheafIso_terminal` and
  `inverseImageProductSheafMap_terminal` show that, for terminal `t` with
  terminal base change, the base-change map is the inverse image of this
  identification.
- For `T : Action S.Etale G` and `σ : t ⟶ T.V`,
  `splittingProjection R T ht σ g F` restricts the product sheaf of `T.V`
  along the graph of `σ ≫ T.ρ g`. `splittingProjection_hom_app` gives its
  value on sections.
- `isLimitSplittingFan` states that, under `TorsorSectionSplitting` for `T`,
  these projections form a limit fan, indexed by `G`, over copies of `F`. The
  proof reflects the limit from presheaves, from evaluation at each object and
  from the forgetful functor to types. There, bijectivity of the cone's
  section map is exactly the assumed splitting bijection on sections over `U`,
  viewed as an object over `T.V` through `σ`.
- `isIso_inverseImageProductSheafMap_of_section` states that for finite `G`,
  if `T` and its base change along `f` both satisfy the splitting property,
  then `c_f T.V F` is an isomorphism. Inverse image preserves the finite
  product, and the base-change map commutes with the two limit fans by
  `inverseImageProductSheafMap_coverPullback` and the terminal case.
  Mathlib's `IsLimit.hom_isIso` then applies.

## Finite geometric torsors

- `isIso_coverPullback` states that restriction along an isomorphism of cover
  objects is invertible.
- `isIso_inverseImageProductSheafMap_comp_iff` states that, when the map for
  `g` is invertible, the map for `g ≫ f` is invertible if and only if
  `g^*(c_f V F)` is. It follows from the composition law.
- `isIso_inverseImageProductSheafMap_of_torsor` states that
  `c_f Y.V F` is an isomorphism for every `Y` with
  `IsFiniteGeometricTorsor X Y`, every morphism `f` and every sheaf `F`. The
  proof restricts to the cover `W' = P_f Y.V` of `Z`. That cover is surjective
  because the existing `IsFiniteGeometricTorsor.pullback` includes
  surjectivity, so the existing `isIso_of_restrictionFamily` and
  `coversTop_of_jointlySurjective` apply. After the existing
  `inverseImageIsoRestriction`, it suffices that `j'^*(c_f)` is invertible,
  where `j'` is the étale structure map of `W'`. By the composition law and
  the étale case, this is equivalent to invertibility of the map for
  `j' ≫ f`, which equals `f' ≫ j` by `pullback.condition`, with `j` the
  structure map of `Y.V`. Applying the composition law again, it suffices to
  treat the map for `f'` and the torsor `P_j Y` over `Y.V`. That torsor has
  the diagonal section from the identity terminal object. Both it and its base
  change along `f'` are finite geometric torsors, hence satisfy the splitting
  property by `etaleTorsorSectionSplitting`. The section case applies.
- `inverseImageProductSheafIso` packages the map as an isomorphism, with
  `inverseImageProductSheafIso_hom`.

## Associated sheaves

For `Y` with `hY : IsFiniteGeometricTorsor X Y`, writing `Y_f` for its base
change by `etaleTorsorPullbackFunctor f G`:

- `isIso_inverseImageAssociatedMap_app_of_torsor` states that the existing
  comparison `inverseImageAssociatedMap f R Y` is invertible at every
  coefficient action. It uses the existing finite-group reduction
  `isIso_inverseImageAssociatedMap_app`.
- `inverseImageAssociatedIso f R Y hY` is the natural isomorphism

  ```text
  associatedFunctor X Y ⋙ inverseImage f R
    ≅ (inverseImage f R).mapAction G ⋙ associatedFunctor Z Y_f,
  ```

  with components the existing comparison (`inverseImageAssociatedIso_hom_app`).
- `inverseImageAssociatedIso_hom_inclusion` states that its forward map
  followed by the invariant inclusion for `Y_f` is inverse image of the
  original inclusion followed by `inverseImageProductSheafIso`.
  `inverseImageAssociatedIso_inv_inclusion` states that the inverse map
  followed by inverse image of the original inclusion is the inclusion for
  `Y_f` followed by the inverse of `inverseImageProductSheafIso`.

## Provenance

This is internal infrastructure: adjunction calculus, product and limit
comparisons and reflection of limits in Mathlib, combined with the existing
inverse and direct images, their composition comparisons, the étale
restriction comparisons, the covering criterion for isomorphisms of sheaves,
the base change of finite geometric torsors and the proved torsor splitting
of sections. No external-literature statement is formalized.
