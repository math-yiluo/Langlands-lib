# Derived comparison of right resolutions

This internal categorical construction defines an actual morphism in the
unbounded derived category from an arbitrary right resolution to the right
derived complex. Its provenance is the imported Library modules
`AcyclicResolution.Comparison`, `AcyclicResolution.Lift`, `DerivedPlus`,
`DerivedPlusNaturality` and `ExtendMap`, together with Mathlib's extension of
homotopies and localization of cochain complexes. It introduces no assertion
transcribed from external literature. Worker 606 authored this development.

Let `F : C ⥤ D` be additive, where `C` and `D` are abelian categories with actual
derived localizations and `C` has enough injectives. The object, morphism and
localization universes of the two categories are independent. No exactness of
`F` is assumed. A right resolution is a quasi-isomorphism
`ε : (CochainComplex.single₀ C).obj A ⟶ K` with `K` indexed by the natural numbers.

The functor `derivedResolutionFunctor F` first extends a natural-indexed
complex by zero to the integers, then applies `F` termwise, then applies the
actual localization `DerivedCategory.Q` of `D`. Write this functor as `T`.
For an injective resolution `I` of `A`, `derivedResolutionIso F I` is the
isomorphism

```text
(derivedComplex F ⋙ DerivedCategory.Plus.ι).obj A ≅ T.obj I.cocomplex.
```

It is the composite of the image of `DerivedPlus.derivedComplexIso F I` under
the bounded below inclusion with the component of `Plus.QCompιIso D` at the
bounded below complex `F(I)`. For any cochain map `φ : K ⟶ I.cocomplex`, define

```text
derivedComparison F I φ = T.map φ ≫ (derivedResolutionIso F I).inv.
```

This definition does not need an augmentation. The augmentation and its
quasi-isomorphism property enter the coherence lemmas. The canonical
`derivedResolutionComparison F ε` uses Mathlib's chosen
`injectiveResolution A` and the published `lift ε (𝟙 A)`.

For compatible lifts `φ` and `ψ`, `derivedComparison_eq` proves independence
of both the lift and the injective resolution. More generally, suppose
`η : B[0] ⟶ L`, `f : A ⟶ B` and `g : K ⟶ L` satisfy
`ε ≫ g = (single₀ C).map f ≫ η`, and `φ`, `ψ` commute with their augmentations.
Then `derivedComparison_naturality` proves

```text
T.map g ≫ derivedComparison F J ψ =
  derivedComparison F I φ ≫ (derivedComplex F ⋙ Plus.ι).map f.
```

This result needs `QuasiIso ε`; it does not need `QuasiIso η` when the two lifts
are already given. The canonical naturality theorem assumes both right
resolutions so their canonical lifts exist. The proof uses the published
`DerivedPlus.descHom f I J` and `homotopyOfComp` to compare the two composites
into `J`. Extending this homotopy, applying `F`, and localizing makes the maps
equal. Naturality of `derivedResolutionIso` follows from the published
`derivedComplexIso_hom_naturality` and `Plus.QCompιIso` naturality. Independence
is the case `f = 𝟙 A`, `g = 𝟙 K`.

The cohomology identifications are specified rather than chosen arbitrarily.
For `n : ℕ`, `derivedResolutionHomologyIso F K n` identifies
`Hⁿ(T.obj K)` with `Hⁿ(F(K))` as the composite of:

1. `DerivedCategory.homologyFunctorFactors D (n : ℤ)` at `F(K extended)`;
2. the homology functor applied to the inverse of
   `DerivedPlus.mapExtendIso F K embeddingUpNat`;
3. `(F(K)).extendHomologyIso embeddingUpNat rfl`.

Denote this source isomorphism by `s_K`. The target is exactly the published
`DerivedPlus.homologyIso F I n`, denoted by `t_I`. The theorem
`derivedComparison_homology` proves the explicit equality

```text
Hⁿ(derivedComparison F I φ) ≫ t_I.hom =
  s_K.hom ≫ AcyclicResolution.comparison F I φ n.
```

Here `comparison` is the existing degreewise map to `(F.rightDerived n).obj A`.
Consequently `derivedResolutionComparison_homology` identifies the homology
map of the canonical derived comparison with the already published
`resolutionComparison F ε n`, using `I = injectiveResolution A`. These
formulas hold in every nonnegative degree and do not assume acyclicity of the
terms of `K` under `F`.

The proof first establishes naturality of `s_K` from naturality of the
localization homology comparison, `extendMapIso_hom_naturality`, and
`extendHomologyIso_hom_naturality`. Expanding the definitions then shows
`Hⁿ(derivedResolutionIso F I).hom ≫ s_I.hom ≫
(I.isoRightDerivedObj F n).inv = t_I.hom`. Applying this identity to the
definition of `derivedComparison` cancels the resolution isomorphism and
leaves exactly naturality of `s_K` followed by the existing definition of
`comparison`.

This module provides maps and their coherence. It does not prove that the
comparison is an isomorphism, construct the comparison for a composite of
functors, or establish geometric perfect base change. Those are separate
mathematical obligations.
