# Derived complexes of exact composites

Author: Worker 727.

Module `Langlands.Cohomology.DerivedExactComposition`, namespace
`Langlands.Cohomology.DerivedPlus`. It extends the Library module
`Langlands.Cohomology.DerivedExactPostcomposition` (exact postcomposition of
actual derived complexes) in three directions:

1. a natural isomorphism `G ≅ H` of additive functors induces a natural
   isomorphism of their actual derived complexes, and so an exact `P` with
   `G ⋙ P ≅ H` gives `ι(R G) ⋙ P.mapDerivedCategory ≅ ι(R H)`;
2. cohomology of `P.mapDerivedCategory` is `P` applied to cohomology, as a
   natural isomorphism;
3. on cohomology in degrees `n : ℕ`, the isomorphism of (1) is the classical
   comparison `P (Rⁿ G X) ≅ Rⁿ H X` computed with one injective resolution.

Everything is proved in the file, with no hypotheses beyond those in the
signatures and no proof holes. The module states no further properties.

## Conventions

`C`, `D`, `E` (and `F` in the last section) are abelian categories in
arbitrary, independent universes. Where derived categories occur they are
Mathlib's chosen ones (`HasDerivedCategory`), and `C` has enough injectives.
`ι` is `DerivedCategory.Plus.ι`, `Q` is `DerivedCategory.Q`.
`derivedComplex G : C ⥤ DerivedCategory.Plus D` is the Library's actual right
derived functor of an additive `G : C ⥤ D`, and `homologyIso G I n` is the
Library's identification of its `n`-th cohomology with `(G.rightDerived n).obj X`
for an injective resolution `I` of `X` (module `Langlands.Cohomology.DerivedPlus`).
From the Library module `Langlands.Cohomology.AcyclicResolution.DerivedComparison`:
`derivedResolutionFunctor G` sends a complex `K : CochainComplex C ℕ` to
`Q (G (K.extend ℕ→ℤ))`, `derivedResolutionIso G I : ι((derivedComplex G).obj X) ≅
(derivedResolutionFunctor G).obj I.cocomplex`, and `derivedResolutionHomologyIso`
computes its cohomology. "Exact" for `P : D ⥤ E` means additive, preserving
finite limits and finite colimits.

## Section `Congr`: natural isomorphisms of functors

Let `G H : C ⥤ D` be additive and `e : G ≅ H`.

- `resolutionCongrNatIso e : derivedResolutionFunctor G ≅ derivedResolutionFunctor H`
  is `Q` applied to Mathlib's termwise isomorphism
  `NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)`, after extension.
- `derivedComplexCongrOfResolution e I` is the isomorphism
  `ι((derivedComplex G).obj X) ≅ ι((derivedComplex H).obj X)` obtained by
  conjugating `(resolutionCongrNatIso e).app I.cocomplex` with
  `derivedResolutionIso G I` and `derivedResolutionIso H I`.
- `derivedComplexCongrOfResolution_hom_naturality`: for `f : X ⟶ Y` and a
  morphism `φ : InjectiveResolution.Hom I J f` of injective resolutions over
  `f`, the square with `ι(derivedComplex G).map f` and
  `ι(derivedComplex H).map f` commutes. Proof: the Library's
  `derivedResolutionIso_hom_naturality` for `G` and `H`, and naturality of
  `resolutionCongrNatIso e`.
- `derivedComplexCongrOfResolution_hom_eq`: independence of the resolution
  (the previous lemma with the Library's lift `descHom (𝟙 X) I J`).
- `derivedComplexCongr e : derivedComplex G ⋙ ι ≅ derivedComplex H ⋙ ι`, the
  natural isomorphism with components computed with Mathlib's chosen
  injective resolutions; `derivedComplexCongr_hom_app` gives its component
  with any injective resolution, and `derivedComplexCongr_hom_resolution`
  states that it is `resolutionCongrNatIso e` after transport to the
  resolution models.

## Section `Comp`: exact composites

For additive `G : C ⥤ D`, exact `P : D ⥤ E`, additive `H : C ⥤ E` and
`e : G ⋙ P ≅ H`:

```text
derivedCompIso G P e :
  (derivedComplex G ⋙ ι) ⋙ P.mapDerivedCategory ≅ derivedComplex H ⋙ ι
```

is the composite of the Library's `derivedPostcompIso G P` with
`derivedComplexCongr e`. `derivedCompIso_hom_resolution` gives it in the
resolution models: `P.mapDerivedCategory` of `derivedResolutionIso G I`, then
the Library's `resolutionPostcompNatIso G P`, then `resolutionCongrNatIso e`.

## Section `Homology`: cohomology of an exact functor on derived categories

For exact `P : D ⥤ E`:

- `mapHomologicalComplexHomologyIso P c i :
  P.mapHomologicalComplex c ⋙ homologyFunctor E c i ≅ homologyFunctor D c i ⋙ P`,
  with components Mathlib's `ShortComplex.mapHomologyIso` (simp lemma
  `mapHomologicalComplexHomologyIso_hom_app`).
- Two `Localization.Lifting` instances (`mapDerivedCategoryHomologyLifting`,
  `homologyFunctorCompLifting`) for the localization `Q` at quasi-isomorphisms,
  built from Mathlib's `P.mapDerivedCategoryFactors` and
  `DerivedCategory.homologyFunctorFactors`.
- `mapDerivedCategoryHomologyIso P n :
  P.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor E n ≅
  DerivedCategory.homologyFunctor D n ⋙ P` for `n : ℤ`, the natural isomorphism
  induced by `mapHomologicalComplexHomologyIso` through Mathlib's
  `Localization.liftNatIso`.
- `mapDerivedCategoryHomologyIso_hom_app_Q_obj`: its component at `Q K` is the
  explicit composite of the factorization isomorphisms with
  `((K.sc n).mapHomologyIso P).hom`.
- `mapDerivedCategoryHomologyIso_hom_naturality`: its naturality square, with
  an `_assoc` form.

## Technical sections `Extend`, `ExtendComp`, `CompHomology`, `MapComp`

These lemmas compare Mathlib's homology comparison `mapHomologyIso` of an
exact functor with the other identifications used above.

- `homologyπ_mapHomologyIso_hom`: for a short complex `S`,
  `(S.map P).homologyπ ≫ (S.mapHomologyIso P).hom =
  (S.mapCyclesIso P).hom ≫ P.map S.homologyπ`.
- `map_extendXIso_hom`, `mapCyclesIso_hom_map_extendCyclesIso_hom`,
  `mapHomologyIso_hom_map_extendHomologyIso_hom`: compatibility of the
  termwise comparison `mapExtendIso` of the Library (module
  `Langlands.Cohomology.DerivedPlus`) and of the cycles and homology
  comparisons of `P` with Mathlib's `extendXIso`, `extendCyclesIso` and
  `extendHomologyIso`, for any embedding of complex shapes.
- `mapExtendIso_comp_inv`: the inverse of `mapExtendIso (F ⋙ P)` is the
  composite of the inverses for `F` and for `P`.
- `resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app`,
  `mapHomologicalComplexCompIso_hom_app_extend_comp` and
  `resolutionPostcompCongr_homology`: in the resolution models, the combined
  map `resolutionPostcompNatIso ≫ resolutionCongrNatIso` is
  `P.mapDerivedCategoryFactors` followed by `Q` of
  `Functor.mapHomologicalComplexCompIso e`, and its `n`-th cohomology
  (`n : ℕ`) is `mapDerivedCategoryHomologyIso`, then `P` of
  `derivedResolutionHomologyIso G`, then the inverse homology comparison of
  `P`, then the homology of `Functor.mapHomologicalComplexCompIso e` on the
  natural-indexed complex.
- `mapCyclesIso_comp_hom`, `mapHomologyIso_comp_hom`: for exact `A` and `B`,
  the cycles and homology comparisons of `A ⋙ B` are those of `B` (on `S.map A`)
  followed by `B` applied to those of `A`.

## Section `RightDerivedComp`: the classical comparison

Assume `C` has injective resolutions (no derived categories are needed). For
additive `G`, exact `P`, additive `H`, `e : G ⋙ P ≅ H`, an injective
resolution `I` of `X` and `n : ℕ`,

```text
rightDerivedCompIsoOfResolution G P e I n :
  P.obj ((G.rightDerived n).obj X) ≅ (H.rightDerived n).obj X
```

is `P` of Mathlib's `I.isoRightDerivedObj G n`, then the inverse of the
homology comparison of `P` on `G(I)`, then the homology of
`Functor.mapHomologicalComplexCompIso e` on `I`, then the inverse of
`I.isoRightDerivedObj H n`. `rightDerivedCompIsoOfResolution_hom` and
`_inv` state these composites. `compIsoOfResolution_id_hom` shows that with
the identity as the middle functor it agrees with the Library's
`DerivedComparison.compIsoOfResolution G P (𝟭 C) H (e ≪≫ H.leftUnitor.symm) I n`.

## Section `CompHomologyIso`: cohomology of `derivedCompIso`

With the hypotheses of section `Comp`, an injective resolution `I` of `X`
and `n : ℕ`:

- `derivedCompIso_hom_homology`: the `n`-th cohomology of
  `(derivedCompIso G P e).hom.app X`, followed by `homologyIso H I n`, equals
  `(mapDerivedCategoryHomologyIso P n).hom.app` at `ι((derivedComplex G).obj X)`,
  followed by `P.map (homologyIso G I n).hom` and
  `(rightDerivedCompIsoOfResolution G P e I n).hom`.
- `derivedCompIso_inv_homology`: the corresponding identity for the inverse.

Here the cohomology of an object of `DerivedCategory.Plus` used by
`homologyIso` is, by definition, the cohomology of its image under `ι`.

## Section `RightDerivedCompCoherence`

`rightDerivedCompIsoOfResolution_hom_comp`: let `Γ : C ⥤ D` be additive, `A`,
`B` and `Ac` exact, `c : Ac ≅ A ⋙ B`, and `eG : Γ ⋙ A ≅ G`,
`eH : Γ ⋙ Ac ≅ H`. Then the classical comparison for `G` and `B` along the
isomorphism `G ⋙ B ≅ H` assembled from `eG`, `c` and `eH` equals
`B.map` of the inverse comparison for `Γ, A, eG`, followed by
`c.inv.app ((Γ.rightDerived n).obj X)` and the comparison for `Γ, Ac, eH`.
The proof reduces to `mapHomologyIso_comp_hom` and Mathlib's
`NatTrans.app_homology` and `ShortComplex.homologyMap_comp`.

## Provenance

Internal. These are standard facts of homological algebra: an exact functor
commutes with cohomology, and derived functors are functorial in natural
isomorphisms of the underlying functor. No literature statement is
formalized or cited. The Lean declarations are derived directly from the Library's
`derivedPostcompIso`, `derivedResolutionIso` and
`DerivedComparison.compIsoOfResolution`, and from Mathlib's
`Localization.liftNatIso`, `Functor.mapDerivedCategoryFactors` and
`ShortComplex.mapHomologyIso`. No external mathematical assertion is used.
