# Bounded-below derived global sections on the small-etale site

Author: Worker 13.

This is internal derived infrastructure specializing the published
[`DerivedPlus`](../Cohomology/DerivedPlus.md) and
[`DerivedPlusNaturality`](../Cohomology/DerivedPlusNaturality.md) constructions
to the actual section functor of
[`EtaleDerivedSections`](EtaleDerivedSections.md). Its definitions and
comparisons are implementations of those existing constructions; no new
external source assertion is made.

## Setting and construction

Let `X : AlgebraicGeometry.Scheme.{u}` and let `R : Type u` be a commutative
ring. The coefficient category is
`ModuleSheaf X R = Sheaf X.smallEtaleTopology (ModuleCat.{u} R)`.
Its enough-injectives instance is supplied by Mathlib's Grothendieck-abelian
construction for the actual small-etale site. It is not an extra premise.
The section functor is the existing `EtaleDerivedSections.sections X R`,
the right adjoint to constant sheafification; its existing comparison with
evaluation at the terminal etale object gives its global-section meaning.
It is additive and preserves finite limits.

The two derived-category choices are explicit and independent:
`[HasDerivedCategory.{wS} (ModuleSheaf X R)]` and
`[HasDerivedCategory.{wT} (ModuleCat.{u} R)]`. Mathlib's standard choices are
available. Both localize integer-indexed cochain complexes, and `Plus` is
the full subcategory of cohomologically bounded-below objects. All section
maps are `R`-linear.

`rightDerivedFunctor` is precisely
`(sections X R).rightDerivedFunctorPlus`, from the bounded-below derived
category of sheaves to that of modules. `derivedSections` places a sheaf in
degree zero and applies that functor. It reuses `DerivedPlus.derivedComplex`.
Thus it gives objects and coefficient maps in an actual derived category.

## Resolution representatives and maps

For a sheaf `F`, `complex F` is the actual bounded-below complex obtained by
extending Mathlib's chosen injective resolution of `F` from natural to integer
cochain degrees, by zero in negative degrees, and then applying global
sections term by term. `resolutionIso I` identifies derived sections of `F`
with the localization of the section complex of any injective resolution
`I : InjectiveResolution F`. `complexIso F` uses the chosen resolution.
Both reuse the proved `DerivedPlus.derivedComplexIso`.

`complexMap f` takes Mathlib's chosen lift of a sheaf morphism to its chosen
injective resolutions, extends the cochain map to integer degrees, and
applies sections. No strict functor structure on these chosen raw complexes
is supplied. `resolutionIso_hom_naturality` identifies the derived map
with the localized map of section complexes for every compatible map of
resolutions, using the published generic naturality theorem.
`complexIso_hom_naturality` specializes this to `complexMap f`. Consequently
these localized maps satisfy identity and composition through their
identification with the actual `derivedSections` functor.

## Cohomology and diagrams

For `q : ℕ`, `homologyNatIso q` is a natural isomorphism

```text
derivedSections X R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat R) q
  ≅ EtaleDerivedSections.cohomology X R q.
```

It reuses `DerivedPlus.homologyNatIso`, so its naturality holds for all
coefficient maps. `homologyNatIso_hom_app I q` identifies its component with
the generic comparison computed using any injective resolution `I`.
`homologyZeroIso` composes the degree-zero comparison with the existing
zeroth-cohomology/global-section isomorphism.
`isZero_homology_of_neg F hq` reuses the generic negative-degree vanishing
for a sheaf placed in degree zero.

For a category `K` with independent object and morphism universes `uK`
and `vK`, `diagramFunctor K` postcomposes coefficient diagrams with
`derivedSections X R`. Maps of diagrams are transported by whiskering.
This applies derived sections separately at each entry; it does not take
a derived inverse limit.

## Scope

This unit concerns ordinary global sections, with fixed module scalars, on
the actual small-etale site of a supplied scheme. It supplies neither
compact support, geometric group or Galois actions, inverse-limit
comparisons, smooth representations, nor the Harris Shimura schemes and
their uniformization. Its Harris specialization is documented separately in
[`HarrisEtaleDerivedPlus`](../Shimura/Coefficients/HarrisEtaleDerivedPlus.md).
