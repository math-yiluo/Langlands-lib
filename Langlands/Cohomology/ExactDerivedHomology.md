# Homology of an exact functor on derived categories

Author: Worker 13.

This internal construction descends the canonical homology comparison
for an exact functor between abelian categories to their unbounded
derived categories. The result is a natural isomorphism on the whole
derived category, including its localized morphisms.

## Inputs and provenance

The inputs are abelian categories `C : Type uC` and `D : Type uD`
with morphisms in independent universes `vC` and `vD`, and an additive
functor `F : C ⥤ D` that preserves finite limits and finite colimits.
Chosen derived categories have morphism universes `wC` and `wD`,
specified by Mathlib's `HasDerivedCategory` instances. These instances
choose actual localizations at quasi-isomorphisms. Mathlib constructs
`HasDerivedCategory.standard` at the maximum of the object and morphism
universes; no smallness theorem for derived morphisms is presumed here.

The construction uses the published
`Langlands.Cohomology.mapHomologicalComplexHomologyIso` from
`DivisibleSystem.InverseLimit`. Only that general categorical
isomorphism is used; none of that module's inverse-limit theorems or
finiteness assumptions is invoked. Mathlib's
`Algebra/Homology/DerivedCategory/ExactFunctor.lean` supplies the actual
functor `F.mapDerivedCategory` and its comparison with termwise
application of `F`. Its `HomologySequence.lean` supplies derived
homology and its localization comparison. The descent uses
`CategoryTheory/Localization/Predicate.lean`. These Mathlib files are
pinned at `5ed2965256430c3649e86755f9576b54eca72435`.
This is an internal derivation from those constructions, without a new
external literature claim.

## Constructed comparison

For any integer `q`, write `Hq_C` and `Hq_D` for Mathlib's homology
functors on the two derived categories, and write `Q_C` and `Q_D` for
the localization functors on integer-indexed cochain complexes.

`exactDerivedHomologyIsoOnComplexes F q` is the isomorphism

```text
Q_C ⋙ (F.mapDerivedCategory ⋙ Hq_D)
  ≅ Q_C ⋙ (Hq_C ⋙ F).
```

It first uses `F.mapDerivedCategoryFactors` to represent the derived
image by the termwise image complex. The derived homology comparison
then computes its homology on that complex. The existing canonical
exact-functor homology isomorphism identifies this with `F` of the
original complex's homology. The inverse localization comparison for
`C` finishes the construction.

`exactDerivedHomologyIso F q` descends this isomorphism along `Q_C`:

```text
F.mapDerivedCategory ⋙ Hq_D ≅ Hq_C ⋙ F.
```

Localization gives fully faithful precomposition by `Q_C`, so the
descent acts on all derived morphisms. The theorem
`exactDerivedHomologyIso_hom_app_Q_obj` states that its component on
`Q_C.obj K` is the original comparison on the cochain complex `K`.
`exactDerivedHomologyIso_naturality` states the corresponding equation
for any derived morphism `f : K ⟶ L`, with a reassociated variant.

## Scope

This concerns ordinary homology of integer-indexed complexes and their
localization at quasi-isomorphisms. No injective or projective
resolution, enough-injectives hypothesis, boundedness condition or
inverse-limit preservation is needed. It provides no global-section,
compact-support, completed-cohomology or geometric comparison theorem.
The Harris specialization still requires the actual geometric input
and its already constructed exact association functor.
