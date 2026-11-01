# Geometric normalization of derived global pullback

Author: Worker 13.

This internal construction gives ordinary geometric section pullback and its
termwise map on bounded-below complexes. It proves that the already
constructed derived global pullback recovers this same map through the
actual localization and right-derived comparisons.

## Inputs and provenance

The scheme morphism `f : Z ⟶ X` is arbitrary. Both schemes, the commutative
coefficient ring `R : Type u` and module carriers share universe `u`. The
sheaves and section functors are the actual small-etale constructions.
The ordinary and termwise section maps need no chosen derived categories.
The normalization theorem uses chosen actual derived-category localizations
with independent morphism universes `wX`, `wZ` and `wR`.

The file imports `EtaleDerivedGlobalPullback`, reuses its actual geometric
and derived functors, and makes no new external literature claim. Its
provenance is the constructed ordinary inverse/direct adjunction and
terminal-section comparison, the constructed bounded-below derived
adjunction and its normalization, and the existing global comparison's
right-derived unit equation. These use pinned Mathlib
`CategoryTheory/Adjunction/Restrict.lean`,
`CategoryTheory/Functor/Derived/Adjunction.lean`,
`CategoryTheory/Functor/Derived/RightDerived.lean`, and the complex and full
subcategory functors at commit
`5ed2965256430c3649e86755f9576b54eca72435`.

## Ordinary and complex maps

`sectionsPullback` is the natural transformation

```text
Γ_X ⟶ inverseImage f R ⋙ Γ_Z.
```

It first applies `Γ_X` to the actual ordinary adjunction unit
`F → f_*(inverseImage F)`, then uses the actual terminal-section comparison
`Γ_X f_* ≅ Γ_Z` at `inverseImage F`. The functor associator and left unitor
give the exact displayed domain and target.

`sectionsComplexPullback` applies the corresponding construction to
bounded-below complexes: the restricted termwise geometric adjunction
supplies its unit, and `sectionsComplexIso` supplies the termwise section
comparison. It is a natural transformation

```text
Γ_X.mapCochainComplexPlus
  ⟶ inverseImage.mapCochainComplexPlus ⋙ Γ_Z.mapCochainComplexPlus.
```

The private `complexPlus_unit_hom` identifies the underlying restricted
complex unit with the degreewise ordinary adjunction unit. Its proof uses
the fully faithful adjunction restriction formula and the reflexive complex
inclusion comparisons. The theorem `sectionsComplexPullback_app_f`
consequently proves that, in every integer degree `i`, the complex map is
exactly `sectionsPullback` at the original sheaf `K.obj.X i`. The proof also
uses the fully faithful inclusion's preimage equation for the termwise
section isomorphism.

## Derived normalization

Write `β_X` and `β_Z` for the actual right-derived global-section units,
`α_K` for `EtaleDerivedInverseImage.plusFactors` at a bounded-below complex
`K`, and `θ` for the constructed derived global pullback.
The theorem `derivedPullback_normalization` states

```text
β_X(K) ≫ θ(Q_X K) ≫ RΓ_Z(α_K)
  = Q_R(sectionsComplexPullback(K)) ≫ β_Z(inverseImage K).
```

This holds for every bounded-below complex, with no injectivity condition on
its terms. The appearances of `α` and `β` are the actual constructed
comparison maps, rather than assumed normalization data.

The private `composite_unit_normalized` first rewrites the global comparison's
unit equation by cancelling the invertible termwise section comparison.
The main proof uses naturality of the derived global comparison at `α_K`,
then the derived adjunction's `unit_app_Q` equation. Functoriality combines
the resulting derived-section maps. Naturality of the section-derived unit
at the ordinary termwise adjunction unit moves that unit to the original
section complex. The private composite-unit equation finishes the
identification. The remaining composite is precisely localization of
`sectionsComplexPullback`.

## Scope

There are no etale, affine, flatness, finite-type or Noetherian hypotheses.
No preservation of injectives by inverse image or exactness of direct image
is used. This proves a normalization on complex representatives. The
degree-zero identification on the published ordinary cohomology functors,
geometric identity/composition for the derived maps, agreement with the
older etale-restriction model, coefficient-ring coherence, compact supports,
smooth actions and Harris specialization remain separate obligations.
