# The derived comparison for composite functors

This is internal categorical infrastructure constructed from the Library's
`AcyclicResolution.DerivedComparison`, `DerivedPlus`, `ExtendMap`, and the generic
parts of `Modules.PushforwardComparison` and `Modules.CohomologyBaseChange`.
It introduces no new assertion transcribed from external literature.

Let `C`, `D`, and `E` be abelian categories, with enough injectives in `C` and
`D`. Their object universes, morphism universes, and derived localization
universes are independently quantified. Let `F : C ⥤ D`, `G : D ⥤ E`, and
`H : C ⥤ E` be additive, with a specified natural isomorphism
`e : F ⋙ G ≅ H`. The source-model constructions use additivity; the
acyclic-object comparison also assumes that `F` preserves finite limits.
There is no left exactness assumption on `G`.

For an object `A : C`, assume

```text
hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A).
```

The selected definition is an actual morphism in the derived category of `E`:

```text
derivedCompComparison G e A hA :
  (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).obj A ⟶
  (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).obj (F.obj A).
```

Here the derived complexes are the published right derived functors of
objects placed in degree zero, included into the unbounded derived category.

## The specified source model

For a natural-indexed cochain complex `K`, put `FK = F(K)` degreewise and
write `ext` for extension by zero along `embeddingUpNat`. The isomorphism
`compResolutionIso G e K` is the following composite of actual
integer-indexed complex isomorphisms:

```text
H(ext K) ≅ ext(HK) ≅ ext(G(FK)) ≅ G(ext(FK)).
```

The first arrow is the inverse of `DerivedPlus.mapExtendIso H K`.
The second is the extension of the inverse component of
`Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)`.
The third is `DerivedPlus.mapExtendIso G FK`.
The definition `derivedCompResolutionIso` applies the actual localization
functor `DerivedCategory.Q` to this specified composite.

`compResolutionIso_hom_naturality` combines the naturality of the first
extension comparison, the inverse termwise composite comparison, and the
last extension comparison. Applying localization proves
`derivedCompResolutionIso_hom_naturality`.

## The acyclic-object comparison and coherence

For any injective resolution `I` of `A`,
`quasiIso_mapAugmentation F I hA` makes `mapAugmentation F I` a
quasi-isomorphism from the degree-zero complex of `F A` to `F I`.
The definition `derivedCompComparisonWithResolution G e I hA` composes

```text
RH(A) ⟶ Q(H(ext I)) ⟶ Q(G(ext(F I))) ⟶ RG(F A).
```

The first arrow is the hom of `derivedResolutionIso H I`, the second
is the hom of the specified source-model isomorphism, and the last is
`derivedResolutionComparison G (mapAugmentation F I)`.
This last arrow compares the right resolution `F I` with the actual
derived complex of `F A`; it is not assumed to be an isomorphism.

For a supplied morphism `φ : InjectiveResolution.Hom I J f`, the theorem
`derivedCompComparisonWithResolution_naturality` combines the naturality
of the resolution model, the source-model isomorphism, and the
right-resolution comparison. The published `mapAugmentation_naturality`
supplies the augmentation square for the last step.
Taking `f` to be the identity and using the chosen lift `descHom`
proves independence of the injective resolution.

`derivedCompComparison` uses Mathlib's chosen injective resolution of `A`.
The theorem `derivedCompComparison_eq` identifies it with the construction
using any injective resolution. `derivedCompComparison_naturality` states
the square for every `f : A ⟶ B` when both `A` and `B` satisfy the stated
higher-direct-image vanishing.

## The exact cohomology map

For `n : ℕ`, `derivedCompResolutionIso_homology` states that the cohomology
of the source-model isomorphism, transported by
`derivedResolutionHomologyIso` on its two sides, is exactly the homology
map of the inverse termwise composite comparison. Its proof uses
naturality of `DerivedCategory.homologyFunctorFactors`, cancels the
extension comparison for `G`, and applies
`extendHomologyIso_hom_naturality`.

The theorem `derivedCompComparisonWithResolution_homology` then uses the
published cohomology formulas for the resolution model and
`derivedResolutionComparison`. It explicitly gives the map obtained by
composing `I.isoRightDerivedObj H n`, homology of the inverse termwise
composite comparison, and `resolutionComparison G (mapAugmentation F I) n`.

At the chosen source resolution this is the existing `compComparison`.
Precisely, `derivedCompComparison_homology` proves

```text
Hⁿ(derivedCompComparison G e A hA) ≫
  (DerivedPlus.homologyIso G (injectiveResolution (F.obj A)) n).hom
  =
(DerivedPlus.homologyIso H (injectiveResolution A) n).hom ≫
  compComparison G e A hA n.
```

The comparisons in this equality are specified maps, rather than arbitrary
isomorphisms between cohomology objects.

This module constructs the comparison and proves its coherence and cohomology
formula. It gives no isomorphism criterion for the comparison, no geometric
specialization, and no perfect base-change or relative cube theorem.
