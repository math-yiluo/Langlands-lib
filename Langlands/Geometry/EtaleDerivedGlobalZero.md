# Degree-zero normalization of geometric global pullback

This module identifies the degree-zero map of the constructed arbitrary-morphism
small-etale cohomology pullback with ordinary global-section pullback. It also
constructs the singleton complex comparison and proves the normalization through
the actual singleton right-derived units.

## Parameters and provenance

Let `f : Z ⟶ X` be any morphism of `Scheme.{u}` and let `R : Type u` be a
commutative ring. The coefficient categories are the actual small-etale sheaves
`ModuleSheaf X R` and `ModuleSheaf Z R`, with values in `ModuleCat.{u} R`.
The derived statements use chosen derived-category localizations with independent
morphism universes `wX`, `wZ`, and `wR`. The ordinary singleton constructions
need no derived-category choices. There are no etale, affine, flatness,
finite-type, or Noetherian hypotheses on the schemes or their morphism.

This is an internal comparison of already constructed maps. Its inputs are
`EtaleDerivedGlobalPullback.sectionsPullback`,
`sectionsComplexPullback`, and `derivedPullback_normalization`, the actual
inverse-image singleton and localization comparisons, and the generic
`DerivedPlusZero` calculation of the right-derived unit on zeroth homology.
The existing `EtaleDerivedSectionsPlus.homologyZeroIso` is the composition
of its natural homology comparison with
`EtaleDerivedSections.cohomologyZeroIso`.

The underlying pinned Mathlib constructions are the additive functor/singleton
comparison, `Functor.mapDerivedCategorySingleFunctor` and its factorization
identities in `Algebra/Homology/DerivedCategory/ExactFunctor.lean`, naturality
of cycles and homology in `Algebra/Homology/ShortComplex/HomologicalComplex.lean`,
and `Functor.rightDerivedZeroIsoSelf` in
`CategoryTheory/Abelian/RightDerived.lean`. The latter is the inverse of the
canonical ordinary-to-derived map for finite-limit-preserving functors. Here
finite-limit preservation is the existing property of actual global sections.
No desired pullback, comparison, or equality is a supplied parameter.

## Singleton constructions

Write `s(F)` for `DerivedPlus.singlePlus F`, `T` for `inverseImage f R`, and
`Γ_X`, `Γ_Z` for the actual global-section functors.
`inverseImageSingleComplexIso f R F` is the isomorphism

```text
T(s(F)) ≅ s(T(F))
```

obtained by lifting the actual additive functor/singleton comparison through
the fully faithful bounded-below complex inclusion. The private underlying-map
lemma proves that this is exactly the original complex comparison.

`singletonSectionsPullback f R F` composes `sectionsComplexPullback` at `s(F)`
with `Γ_Z` applied to this singleton isomorphism. Its degree-zero component,
as proved by `singletonSectionsPullback_f_zero`, is ordinary section pullback
conjugated by the two actual singleton-term isomorphisms. The proof uses the
published degreewise formula and naturality of ordinary section pullback.

The private `singletonMap_homology` lemma converts that degree-zero formula to
zeroth homology: first cancel the monic cycles inclusion to identify the cycles
map, then use naturality of the cycles-to-homology projection and the generic
singleton cycles/homology comparisons. Localization naturality gives the
corresponding identity for the localized singleton map.

## Normalization of the singleton unit

`plusSingleIso_hom_eq` proves that the existing derived inverse-image singleton
comparison factors as the inverse-image localization comparison followed by
localization of `inverseImageSingleComplexIso`. Its proof applies the faithful
inclusion into the unbounded derived category and the original Mathlib
factorization identity for exact functors. This result needs the two sheaf
localizations, and no module-derived localization.

Write `β_X(F)` for the actual section-derived unit on `s(F)`, `Q` for
localization of bounded-below module complexes, and `p_F` for
`sheafDerivedPullback f R` at `F`. The theorem `sheafDerivedPullback_unit` is

```text
β_X(F) ≫ p_F = Q(singletonSectionsPullback f R F) ≫ β_Z(T(F)).
```

It combines the published normalization on every bounded-below representative
with the singleton factorization above and naturality of the section-derived
unit at the actual singleton isomorphism. No injectivity condition is placed
on `F` or its inverse image.

`sectionUnit_homology_zero` proves

```text
H⁰(β_X(F)) ≫ homologyZeroIso_X(F) = localizedSingleImageHomologyIso_ΓX(F).
```

The generic right-derived unit calculation gives the canonical map
`Γ_X(F) → R⁰Γ_X(F)`. Composing with the inverse canonical isomorphism
`rightDerivedZeroIsoSelf` cancels that map. This theorem only needs the source
sheaf localization and the module localization. It makes zeroth homology of
the singleton section-derived unit invertible; it does not assert that the
unit itself is an isomorphism in the derived category.

## Degree-zero pullback

The main theorem `sheafDerivedPullback_zero` states

```text
H⁰(p_F) ≫ homologyZeroIso_Z(T(F))
  = homologyZeroIso_X(F) ≫ sectionsPullback_f(F).
```

The proof expresses `H⁰(β_X(F))` as a composite of actual isomorphisms using
the preceding unit identity. After cancelling it, functoriality of homology
applied to `sheafDerivedPullback_unit`, the localized singleton-map calculation,
and the two unit identities prove the equation.

Finally, `cohomologyPullback_zero` states the same result on the existing
ordinary cohomology functors:

```text
cohomologyPullback_f^0(F) ≫ cohomologyZeroIso_Z(T(F))
  = cohomologyZeroIso_X(F) ≫ sectionsPullback_f(F).
```

Its proof expands the definition of `cohomologyPullback`, applies the preceding
theorem, and cancels the source natural homology isomorphism. The comparison
uses precisely the existing cohomology-zero isomorphisms, with no new choice
of cohomology model.

This unit establishes degree-zero normalization for arbitrary scheme morphisms.
Geometric identity/composition laws, agreement with the older etale restriction
model, coefficient-ring coherence, compact supports, smooth group actions and
Harris specialization remain separate obligations. The construction uses
neither inverse image preserving injectives nor exactness of direct image.
