# Derived sections and higher direct images of actual scheme modules

Author: Worker 921.

This module applies Mathlib's right-derived functor construction to three
functors on Mathlib's category `X.Modules` of sheaves of modules over the
structure sheaf of a scheme: global sections, global sections over an affine
base `Spec R`, and the existing pushforward `Scheme.Modules.pushforward`.
Everything lives in the namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. The universe `u` is
arbitrary: `X Y : AlgebraicGeometry.Scheme.{u}`, `R : CommRingCat.{u}`, and
all module categories are `ModuleCat.{u}`.

## Injective resolutions

`X.Modules` is `SheafOfModules X.ringCatSheaf`. Mathlib proves that it is
Grothendieck abelian, hence has enough injectives and chosen injective
resolutions. The file only checks that this instance is found
(`example : HasInjectiveResolutions X.Modules`). It adds no
`EnoughInjectives` hypothesis, and no resolution, cohomology module or
comparison is assumed as data.

All derived functors below are Mathlib's `Functor.rightDerived n`. This is
the homology in degree `n` of `Functor.rightDerivedToHomotopyCategory`, which
applies the functor termwise to the chosen injective resolution and works in
the homotopy category of cochain complexes indexed by `ComplexShape.up ℕ`.
A coefficient map `φ : M ⟶ N` in `X.Modules` acts on cohomology through the
functor's `map`, for example `(cohomology X n).map φ`.

## Global sections over `Γ(X, ⊤)`

- `globalSections X : X.Modules ⥤ ModuleCat Γ(X, ⊤)` is
  `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`. It sends a module `M` to
  its sections over the top open, a module over the ring `Γ(X, ⊤)` of global
  functions. The file proves `(globalSections X).Additive` by viewing the
  functor as Mathlib's forgetful functor to presheaves followed by evaluation,
  both of which are additive. `PreservesFiniteLimits (globalSections X)` is
  Mathlib's instance for evaluating sheaves of modules.
- `homotopyFunctor X : X.Modules ⥤ HomotopyCategory (ModuleCat Γ(X, ⊤)) (ComplexShape.up ℕ)`
  is `(globalSections X).rightDerivedToHomotopyCategory`.
- `cohomology X n : X.Modules ⥤ ModuleCat Γ(X, ⊤)` is
  `(globalSections X).rightDerived n`. This is the sheaf cohomology
  `Hⁿ(X, M)` of an actual `𝒪_X`-module, viewed as a `Γ(X, ⊤)`-module.
- `cohomologyZeroIso X : cohomology X 0 ≅ globalSections X` is Mathlib's
  `rightDerivedZeroIsoSelf`. It uses the additivity and finite-limit
  instances above.
- `complex M : CochainComplex (ModuleCat Γ(X, ⊤)) ℕ` applies `globalSections X`
  termwise to `(injectiveResolution M).cocomplex`, Mathlib's chosen injective
  resolution of `M`.
- `complexIso M : (homotopyFunctor X).obj M ≅ (HomotopyCategory.quotient _ _).obj (complex M)`
  and `cohomologyIso M n : (cohomology X n).obj M ≅ (complex M).homology n`
  are Mathlib's `isoRightDerivedToHomotopyCategoryObj` and
  `isoRightDerivedObj` for the chosen resolution.
- `cohomologyIsoOfResolution I n` identifies `(cohomology X n).obj M` with
  the `n`-th homology of `globalSections X` applied to the cocomplex of any
  `I : InjectiveResolution M`.

## Global sections over an affine base, as `R`-modules

Fix `R : CommRingCat.{u}` and `f : X ⟶ Spec R`.

- The file adds two instances for Mathlib's
  `moduleSpecΓFunctor : (Spec R).Modules ⥤ ModuleCat R`. It is a right
  adjoint because it is the right adjoint of `tilde.adjunction`. It is
  additive because, as a right adjoint, it preserves zero morphisms and
  binary products, hence binary biproducts
  (`preservesBinaryBiproducts_of_preservesBinaryProducts`), and Mathlib's
  `Functor.additive_of_preservesBinaryBiproducts` turns that into
  additivity.
- `relativeGlobalSections f : X.Modules ⥤ ModuleCat R` is defined to be the
  composite `Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`. Additivity
  and `PreservesFiniteLimits` hold because both factors are additive right
  adjoints.
- Scalar convention: `moduleSpecΓFunctor` restricts the `Γ(Spec R, ⊤)`-module
  structure to `R` along `(Scheme.ΓSpecIso R).inv`. So `r : R` acts on the
  sections `Γ(M, f ⁻¹ᵁ ⊤)` through the image of `r` in `Γ(X, ⊤)`. The file names this map
  `structureRingHom f : R ⟶ Γ(X, ⊤)`, defined as
  `(Scheme.ΓSpecIso R).inv ≫ f.appTop`.
- `relativeGlobalSectionsIso f :
  globalSections X ⋙ ModuleCat.restrictScalars (structureRingHom f).hom ≅ relativeGlobalSections f`
  is a natural isomorphism whose components are identities. The two
  modules agree definitionally.
- `relativeHomotopyFunctor f`, `relativeCohomology f n :=
  (relativeGlobalSections f).rightDerived n : X.Modules ⥤ ModuleCat R`,
  `relativeCohomologyZeroIso f : relativeCohomology f 0 ≅ relativeGlobalSections f`,
  `relativeComplex f M`, `relativeComplexIso f M`,
  `relativeCohomologyIso f M n : (relativeCohomology f n).obj M ≅ (relativeComplex f M).homology n`,
  and `relativeCohomologyIsoOfResolution f I n` are built for
  `relativeGlobalSections f` in the same way as the global-section versions
  above. `relativeCohomology f n` is the `R`-module cohomology used later,
  for example for line bundles on `R`-schemes.
- `relativeCohomologyRestrictScalarsIso f n :
  cohomology X n ⋙ ModuleCat.restrictScalars (structureRingHom f).hom ≅ relativeCohomology f n`
  says the `R`-module cohomology is the `Γ(X, ⊤)`-module cohomology with
  scalars restricted. It is the Library's
  `Langlands.Cohomology.DerivedComparison.rightDerivedCompIso`, applied with
  `Φ = globalSections X`, exact `P = ModuleCat.restrictScalars`, `T = 𝟭`
  and `Ψ = relativeGlobalSections f`, through `relativeGlobalSectionsIso f`,
  and then composed with the left unitor.

## Higher direct images

Fix `f : X ⟶ Y`. The pushforward is Mathlib's existing
`Scheme.Modules.pushforward f : X.Modules ⥤ Y.Modules`, and this file does not
replace it. Mathlib proves it is a right adjoint (of the pullback) and
additive. The file restates the resulting finite-limit preservation as an
instance.

- `directImageHomotopyFunctor f : X.Modules ⥤ HomotopyCategory Y.Modules (ComplexShape.up ℕ)`
  is `(Scheme.Modules.pushforward f).rightDerivedToHomotopyCategory`.
- `higherDirectImage f n : X.Modules ⥤ Y.Modules` is
  `(Scheme.Modules.pushforward f).rightDerived n`, the higher direct image
  `Rⁿ f_*`.
- `higherDirectImageZeroIso f : higherDirectImage f 0 ≅ Scheme.Modules.pushforward f`.
- `directImageComplex f M : CochainComplex Y.Modules ℕ` is the pushforward of
  Mathlib's chosen injective resolution. `directImageComplexIso f M` and
  `higherDirectImageIso f M n : (higherDirectImage f n).obj M ≅ (directImageComplex f M).homology n`
  give the representative and homology comparisons.
  `higherDirectImageIsoOfResolution f I n` computes `Rⁿ f_* M` from any
  injective resolution `I`.

## Limitations

The representing complexes depend on Mathlib's choice of injective
resolutions. They are functorial only after passing to the homotopy category.
This unit proves none of the following:

- finiteness or coherence of cohomology or of higher direct images;
- the Künneth formula;
- Leray spectral sequences;
- cohomology and base change;
- acyclicity of sheaves with finite support;
- vanishing of cohomology for translation-invariant line bundles.

It also proves no comparison between `relativeCohomology f n` and sections
of `higherDirectImage f n`, no compatibility of higher direct images with
composition, and no comparison with Čech or abelian-sheaf cohomology.

## Provenance

This is internal derived-functor infrastructure. It is not a definition
transcribed from a source. The constructions are the standard
right-derived global sections and higher direct images of sheaves of modules,
implemented with Mathlib's homological algebra. The motivating source is
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary version
of the first chapters (literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`),
printed pp.105-106 (PDF pp.109-110). There:

- Lemma (7.19) uses `Hⁱ(X, L)` for line bundles on an abelian variety and on
  `X × X`.
- Fact (7.20) uses `R^q f_*(F)` for coherent `F` and proper `f`.
- Proposition (7.21) uses Leray spectral sequences with terms
  `Hᵖ(X, R^q p_{i,*}(K))` for both projections `X × X → X`.

This file supplies only the functors `Hⁿ(X, -)` and `Rⁿ f_*` that those
statements mention. Their hypotheses and conclusions are left to later
statement tasks. Worker 921 read both cited pages.

Formal dependencies: Mathlib `5ed2965256430c3649e86755f9576b54eca72435` with
Lean 4.34.0, especially `Mathlib.AlgebraicGeometry.Modules.Sheaf`,
`Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` and
`Mathlib.CategoryTheory.Abelian.RightDerived`; and the Library module
`Langlands.Cohomology.DerivedComparison`.
