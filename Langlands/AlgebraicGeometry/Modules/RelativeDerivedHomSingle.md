# The relative derived sections/Hom comparison on a module in degree zero

This module proves one comparison between constructions that already exist in the
Library. It is supporting work for
`Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison.RelativeAbelianSheafCohomologyPullbackStatement`
(Task 6104). It does not prove that statement.

## Main result

`AbelianSheafComparison.relativeDerivedHomComparison_single`.

Data:

- `R` is a commutative ring and `X` is a scheme over `Spec R` (`X : Over (Spec R)`).
- `M` is an `𝒪_X`-module, `n : ℕ`, and `x ∈ Hⁿ(X, M) = Ext^n(ℤ_X, M)` (Mathlib's `Sheaf.H`) is a
  class of the underlying abelian sheaf of `M`.

Notation:

- `F = relativeGlobalSections X.hom`: the `R`-module global sections functor.
- `G` forgets the `R`-module structure.
- `U = toAbSheaf X.left`: the underlying abelian sheaf.
- `Z = constantIntegers`: the constant sheaf `ℤ_X`.
- `relativeDerivedHomComparison X.hom n` is the published natural transformation
  `G(Hⁿ(RF K)) ⟶ Hom_{D(Ab(X))}(Z, U(K)[n])` on the bounded below derived category
  (module `RelativeDerivedHomComparison`).

The theorem evaluates this transformation at the object `M[0]`, on the element

`(DerivedPlus.homologyIso F (injectiveResolution M) n).inv (relativeHAddEquiv X.hom M n x)`.

It states that the result is `x.hom ≫ (singleToAbSheafIso M).inv⟦n⟧'`. Here:

- `relativeHAddEquiv` is the Library's additive comparison of `Ext`-defined sheaf cohomology with
  relative module cohomology.
- `DerivedPlus.homologyIso` is the Library's identification of the cohomology of the derived
  complex with `F.rightDerived n`.
- `x.hom` is Mathlib's derived-category morphism of the Ext class.
- `singleToAbSheafIso M : U(M[0]) ≅ (U M)[0]` combines `DerivedCategory.Plus.singleFunctorιIso` with
  Mathlib's `Functor.mapDerivedCategorySingleFunctor`.

In words: on a module placed in degree zero, the derived comparison is the inverse of the
relative additive comparison, followed by the identification of Ext classes with
derived-category morphisms.

## General lemmas

`EquivariantComposite.homologyDerivedMap_eq_ext_hom` holds in any abelian category with derived
category and `Ext`. Its data:

- `P` is a complex and `ε : Y[0] ⟶ P` is a quasi-isomorphism.
- `I` is an injective resolution of `Y`, and `φ : P ⟶ I` is a chain map with `ε ≫ φ = I.ι'`.
- `v ∈ Hⁿ(Hom(A, P))`, and `a ∈ Ext^n(A, Y)` is the class whose cohomology class is
  `Hⁿ(Hom(A, φ)) v`.

The conclusion is that the canonical cycle-localization map sends `v` to
`a.hom ≫ (Q ε)[n]`. The proof cancels the isomorphism `(Q φ)[n]` and uses
`homologyDerivedMap_naturality` and Mathlib's
`InjectiveResolution.extEquivCohomologyClass_symm_mk_hom`. No injectivity of `P` is needed.

The namespace `DerivedSectionsHomComparison` holds the following general lemmas. They are stated
for arbitrary `F`, `G`, `U`, `Z` and `e` as in `DerivedSectionsHomComparison`.

- `singleMapDerivedIso U X₀ : U(X₀[0]) ≅ (U X₀)[0]` is the degree-zero identification, and
  `resolutionImageAugmentation U R` is `U` applied to the augmentation `R.ι'` of an injective
  resolution.
- `singleMapDerivedIso_inv_comp` shows that `singleMapDerivedIso`, the resolution isomorphism
  `singleIsoOfResolution R` and Mathlib's `mapDerivedCategoryFactors` compose to the localized
  image augmentation.
- `comparison_app_single` uses naturality of `comparison` along `singleIsoOfResolution R` and
  `unit_comparisonOnComplex_app`. It reduces the value of `comparison` at `X₀[0]` to
  `homologyDerivedMap` on `U(R)`.
- `sectionsComplexIso_extend` and `sectionsHomologyIso_extend` compare the integer-indexed
  `sectionsHomologyIso`, followed by an extended lift, with the natural-indexed termwise comparison.
  They use `mapExtendIso`, `extendHomologyIso` and `mapHomologyIso`. This is pure ℕ/ℤ reindexing
  bookkeeping.

## Implemented proof of the main theorem

1. `resolutionLift M` is the Library's comparison lift from `U` of the chosen injective resolution
   of `M` into the chosen injective resolution `J` of `U M`. This is the lift used by
   `AcyclicResolution.compComparison`. `resolutionLiftInt M` is its integer-indexed extension.
   `resolutionImageAugmentation_comp_resolutionLiftInt` checks in degree zero that the augmentation
   composed with this lift is `J.ι'`.
2. `relativeCohomologyIso_hom_eq` unfolds the published `relativeCohomologyIso` on the chosen
   resolutions. `extAddEquivHomology_relativeHAddEquiv` combines this with
   `relativeCohomologyIso_relativeHAddEquiv` and `HAddEquiv_eq_of_resolution`. It identifies
   `extAddEquivHomology ℤ_X J n x` with the image of the relative class under the termwise
   sections/Hom identification and the lift. The chain-level identity is
   `resolutionLift_sectionsHom`.
3. `sectionsHomologyIso_extend` transports this identity to integer-indexed complexes.
   `homologyDerivedMap_eq_ext_hom` then gives
   `homologyDerivedMap = x.hom ≫ (Q(augmentation))[n]`.
4. `comparison_app_single` turns this into the stated value of `relativeDerivedHomComparison`.

## Provenance

This is internal comparison infrastructure. It identifies two existing Library constructions:

- the derived sections/Hom comparison of `DerivedSectionsHomComparison`;
- the additive comparison `relativeHAddEquiv` built from `relativeCohomologyIso` and
  `AbelianSheafDerivedSections.HAddEquiv`.

It is the standard fact that, for an acyclic resolution, the derived-category morphism of a
cohomology class is computed by any cocycle representative. No external literature theorem is
transcribed.
