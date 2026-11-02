# Proper maps on compact-section complexes of smooth equivariant sheaves

This is an internal construction from the actual functors in
`Langlands.Sheaf.Equivariant.ProperSmoothCompactSections`, the ordinary compact
complex comparisons in `Langlands.Cohomology.LocalCompactComparison`, and
Mathlib's homological-complex and homology functors. It applies the existing
smooth compact-section functor and proper spatial transformation termwise,
then takes homology in the existing abelian category of smooth
representations. It does not prescribe the resulting groups as input data.

The accompanying helper
`Langlands.Representation.Category.ExactInclusion` proves finite-limit and
finite-colimit preservation by the inclusion of smooth representations into
all representations. This supplies the actual exact-functor comparison used
here. Its separate Markdown explains the reduction to the published kernel
and cokernel closure results. No exactness of a smooth-part functor is assumed.

## Scope and hypotheses

The coefficient ring `R` is commutative. The ring, group `G`, spaces, and module
carriers share universe `u`. The index type `I : Type t` and the complex shape
`c : ComplexShape I` are arbitrary. Thus this module covers, in particular,
chain and cochain complexes without imposing boundedness.

The group has a topology making it a topological group. Each space has a
`G`-action and continuous translation by every fixed group element, expressed
by `ContinuousConstSMul G X`. Each participating space also has
`HasStableNeighbourhoods G X`, the existing condition that each neighbourhood
of a point contains a neighbourhood invariant under some open subgroup. These
are hypotheses of the imported additive smooth compact-section and
smooth-direct-image constructions. Continuity of the entire action map is
not an additional assumption.

Write `S_X = SmoothTopologicalSheaf R G X`. This is the existing full category
of locally smooth equivariant module sheaves on the transport category of
ordinary open subsets of `X`. Its objects retain their complete original
sheaves and their smoothness proofs. Write `SmRep` for
`Langlands.SmoothRep R G`, and `U : SmRep ⥤ Rep R G` for its full-subcategory
inclusion. Smoothness of a representation means that each vector is fixed by
an open subgroup.

A spatial map is an actual continuous map `f : C(X, Y)` equipped with
`hf : ∀ g x, f (g • x) = g • f x`. Proper pullback additionally requires
Mathlib's `IsProperMap f`. This is Mathlib's continuous proper-map condition,
which in particular makes inverse images of compact sets compact. No
Hausdorffness, local compactness, or surjectivity is assumed.

## Section complexes and their homology

All functors below act on morphisms as well as objects.

* `underlyingComplex : HomologicalComplex S_X c ⥤
  HomologicalComplex (TopologicalSheaf G X (ModuleCat R)) c` applies the
  inclusion forgetting local smoothness.
* `compactComplex : HomologicalComplex S_X c ⥤
  HomologicalComplex SmRep c` applies `smoothSheafCompactSections` to every
  term and differential. Each term consists of **all** sections with compact
  stalk support, with their original group action. Their smoothness is already
  proved by the imported construction.
* `compactComplexToRepIso` identifies `compactComplex ⋙
  U.mapHomologicalComplex c` with `underlyingComplex ⋙
  EquivariantSections.compactComplex`. It is the termwise
  `smoothSheafCompactSectionsToRepIso`, which retains each original section.
* `globalComplex` applies the ordinary global-section complex functor to
  `underlyingComplex`. `forgetSupportComplex` first uses the preceding
  isomorphism and then the actual compact-support submodule inclusions.

For `i : I`, `compactHomology` is `compactComplex` followed by
`homologyFunctor SmRep c i`. Its objects are the actual kernel/image-quotient
homology objects in the smooth abelian category. `globalHomology` is homology
of `globalComplex` in all representations.

`compactHomologyToRepIso` has type

```text
compactHomology X c i ⋙ U ≅
  underlyingComplex X c ⋙ EquivariantSections.compactHomology X c i.
```

Here and in the formulas below, fixed `R` and `G` are suppressed. The
isomorphism first applies the inverse of the exact-inclusion comparison
`DerivedPlus.mapHomologicalComplexHomologyIso U c i`, then takes ordinary
homology of `compactComplexToRepIso`. The theorem
`compactHomologyToRepIso_hom_app` records this factorization on each complex.
Exactness follows from the helper's proved preservation instances, rather
than an assumption about smooth coreflection.

`forgetSupportHomology` uses this isomorphism followed by the ordinary
support-forgetting homology map. `forgetSupportHomology_app` proves that its
component is equivalently the inverse exact-inclusion comparison followed by
homology of `forgetSupportComplex`.

## Smooth direct image and proper chain maps

Let `D_f` denote `directImageComplex c f hf`. It applies the constructed
`SmoothDirectImage.functor f hf` to terms, differentials, and chain maps.
Ordinary direct image need not preserve smooth sheaves: the imported functor
takes its actual smooth subsheaf.

`directImageIdIso` is an isomorphism from the identity complex functor to
`D_id`, obtained by applying the original smooth identity isomorphism termwise.
`directImageCompMap` has type `D_f ⋙ D_g ⟶ D_(g.comp f)`. It applies the original
lax comparison of smooth direct images termwise. No inverse is constructed or
assumed.

`directImageInclusionComplex` is the actual chain inclusion

```text
D_f ⋙ underlyingComplex Y c ⟶
  underlyingComplex X c ⋙ ProperCompactComplexes.directImageComplex c f hf.
```

For `hp : IsProperMap f`, `properComplex` has type

```text
D_f ⋙ compactComplex Y c ⟶ compactComplex X c.
```

It is `NatTrans.mapHomologicalComplex` of
`ProperSmoothCompactSections.natTrans f hf hp`; the sheaf-level naturality
gives the chain-map equation. `properComplex_f` identifies each component with
that original natural transformation. `properComplex_apply` says that its
value on a compact section `s` has original underlying section `s.val.val`:
it forgets precisely the compact-support and smooth-image subtype witnesses.
The proved proper-support preservation is supplied by the imported
sheaf-level map.

`globalComplexMap : D_f ⋙ globalComplex Y c ⟶ globalComplex X c` applies global
sections to the smooth-image inclusion and then the ordinary-direct-image
global-section identification.

`properComplex_comparison` proves that applying `U` to the proper chain map
and then the target `compactComplexToRepIso` is equal to the source comparison
followed by `LocalCompactComparison.pullbackComplex`. The coefficient map of
that ordinary pullback is exactly `directImageInclusionComplex.app F`.
`properComplex_inclusion_triangle` proves compatibility with the actual
support-forgetting chain maps and `globalComplexMap`.

`properComplex_id` says that mapping `directImageIdIso.hom.app F` through
compact sections and then pulling back along the identity gives the identity.
For proper maps `f : X → Y`, `g : Y → Z`, `properComplex_comp` states

```text
compactComplex Z c.map (directImageCompMap f g).app F ≫
    properComplex (g.comp f).app F =
  properComplex g.app (D_f.obj F) ≫ properComplex f.app F.
```

The composite uses the equivariance proof obtained by rewriting `hf` and
`hg`, and properness `hq.comp hp`. The proof compares components on the
original sections. Thus composition retains the genuine lax comparison
rather than replacing it with an isomorphism.

## Proper maps on smooth homology

`properHomology c f hf hp i` is `properComplex` whiskered with the smooth
homology functor:

```text
D_f ⋙ compactHomology Y c i ⟶ compactHomology X c i.
```

`globalHomologyMap` is ordinary homology of `globalComplexMap`.
`properHomology_comparison` proves

```text
U.map (properHomology f i).app F ≫
    (compactHomologyToRepIso X c i).hom.app F =
  (compactHomologyToRepIso Y c i).hom.app (D_f.obj F) ≫
    LocalCompactComparison.pullbackHomology f hf hp
      (directImageInclusionComplex.app F) i.
```

Its proof uses naturality of the inverse exact-inclusion homology
isomorphism and applies ordinary homology to `properComplex_comparison`.
This identifies the actual maps, including the original group actions.

`properHomology_inclusion_triangle` similarly compares support forgetting
after proper smooth homology pullback with support forgetting before
`globalHomologyMap`. Its proof uses `forgetSupportHomology_app`, the same
exact-inclusion naturality, and homology of the proved chain triangle.

`properHomology_id` and `properHomology_comp` are the corresponding identity
and lax-composition laws. They follow by applying smooth homology to the
chain-level equations, using preservation of composition and identity by a
functor.

## Remaining realization obligations

The input complex is supplied. This module neither chooses a resolution nor
asserts that compact sections are exact, that a supplied complex computes a
derived functor, or that separate smooth and ordinary Godement resolutions
agree. It uses ordinary-open equivariant sheaves and makes no analytic,
etale-site, arithmetic, Galois, Shimura, or Harris-specialization comparison.
Those constructions and comparison obligations remain separate.
